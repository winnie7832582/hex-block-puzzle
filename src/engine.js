/* ---- Hex block puzzle engine: cell geometry, placements, board validation, solver ---- */
const ROWS = 4, COLS = 6, NCELL = ROWS * COLS;
const PIECE_IDS = Object.keys(PIECES);
function offsetToAxial(row, col) { return [col - ((row - (row & 1)) >> 1), row]; }
function axialToOffset(q, r) { return [r, q + ((r - (r & 1)) >> 1)]; }
function cellOf(q, r) {
  const [row, col] = axialToOffset(q, r);
  return (row < 0 || row >= ROWS || col < 0 || col >= COLS) ? -1 : row * COLS + col;
}
function cellAxial(c) { return offsetToAxial(Math.floor(c / COLS), c % COLS); }
function rotateAxial(q, r, steps) {
  let x = q, z = r, y = -x - z;
  for (let i = 0; i < steps; i++) [x, y, z] = [-z, -x, -y];
  return [x, z];
}
/* Node shapes of a piece after optional flip (mirror across the E–W axis) and `rot` 60° steps clockwise. */
function orientedNodes(pid, rot, flip) {
  return PIECES[pid].nodes.map(n => {
    let q = n.pos[0], r = n.pos[1], stems = n.stems.slice(), open = n.open;
    if (flip) { q = q + r; r = -r; stems = stems.map(d => (6 - d) % 6); if (open != null) open = (6 - open) % 6; }
    [q, r] = rotateAxial(q, r, rot);
    return { dq: q, dr: r, type: n.type, stems: stems.map(d => (d + rot) % 6),
             open: open == null ? null : (open + rot) % 6 };
  });
}
/* Solver codes: 100 closed ring, 101 two-stem ball, 2+d one-stem ball, 8+d open ring with gap d. */
function nodeCode(n) {
  if (n.type === 'R_CLOSED') return 100;
  if (n.type === 'R_OPEN') return 8 + n.open;
  return n.stems.length === 1 ? 2 + n.stems[0] : 101;
}
/* Piece `pid` with node 0 at axial (q, r); null if any node leaves the board. */
function makePlacement(pid, rot, flip, q, r) {
  const nodes = [];
  for (const n of orientedNodes(pid, rot, flip)) {
    const cell = cellOf(q + n.dq, r + n.dr);
    if (cell < 0) return null;
    const node = { cell, q: q + n.dq, r: r + n.dr, type: n.type, stems: n.stems, open: n.open };
    node.code = nodeCode(node);
    nodes.push(node);
  }
  return { pid, rot, flip, q, r, nodes };
}
const PL = [], PL_PIECE = [], PL_CELLS = [], PL_CODES = [];
const BY_CELL = Array.from({ length: NCELL }, () => []);
const BY_PIECE = PIECE_IDS.map(() => []);
PIECE_IDS.forEach((pid, pi) => {
  const seen = new Set();
  for (let flip = 0; flip < 2; flip++) for (let rot = 0; rot < 6; rot++) for (let c = 0; c < NCELL; c++) {
    const [q, r] = cellAxial(c);
    const pl = makePlacement(pid, rot, flip, q, r);
    if (!pl) continue;
    const sig = pl.nodes.map(n => n.cell * 1000 + n.code).sort((a, b) => a - b).join(',');
    if (seen.has(sig)) continue;
    seen.add(sig);
    const i = PL.length; PL.push(pl); PL_PIECE.push(pi);
    PL_CELLS.push(pl.nodes.map(n => n.cell)); PL_CODES.push(pl.nodes.map(n => n.code));
    BY_PIECE[pi].push(i);
    for (const n of pl.nodes) BY_CELL[n.cell].push(i);
  }
});
function canCoexist(a, b) {
  if (!((a.type === 'B' && b.type === 'R_OPEN') || (a.type === 'R_OPEN' && b.type === 'B'))) return false;
  const ball = a.type === 'B' ? a : b, ring = a.type === 'B' ? b : a;
  return ball.stems.length === 1 && ball.stems[0] === ring.open;
}
function shortName(pid) { return PIECES[pid].name.split(' ')[0]; }
function cellLabel(c) { return `第 ${Math.floor(c / COLS) + 1} 列第 ${c % COLS + 1} 格`; }
/* Same contract as IQLinkEngine.validate_board. */
function validateBoard(placed) {
  const grid = Array.from({ length: NCELL }, () => []);
  for (const p of placed) for (const n of p.nodes) grid[n.cell].push([p.pid, n]);
  const adj = {}; for (const p of placed) adj[p.pid] = new Set();
  for (let c = 0; c < NCELL; c++) {
    const o = grid[c];
    if (o.length > 2) return { valid: false, reason: `${cellLabel(c)}疊了超過 2 個元件`, cell: c };
    if (o.length === 2) {
      if (!canCoexist(o[0][1], o[1][1])) {
        const types = [o[0][1].type, o[1][1].type].sort().join('+');
        const why = types === 'B+R_OPEN' ? '球的連桿沒有對準環的缺口' : '只有「球＋開口環」能疊在同一格';
        return { valid: false, reason: `${shortName(o[0][0])}和${shortName(o[1][0])}在${cellLabel(c)}相撞，${why}`, cell: c };
      }
      adj[o[0][0]].add(o[1][0]); adj[o[1][0]].add(o[0][0]);
    }
  }
  const visited = new Set(), components = [];
  for (const pid in adj) if (!visited.has(pid)) {
    const comp = [], stack = [pid]; visited.add(pid);
    while (stack.length) { const cur = stack.pop(); comp.push(cur);
      for (const nx of adj[cur]) if (!visited.has(nx)) { visited.add(nx); stack.push(nx); } }
    components.push(comp);
  }
  const links = {}; for (const k in adj) links[k] = [...adj[k]];
  return { valid: true, solved: placed.length === 12 && components.length === 1, components, links };
}
/* Backtracking solver. 36 nodes on 24 cells means at least 12 ball-in-ring pairs, so in total at most
   2 one-stem balls, 2 open rings or 2 cells may stay unpaired/empty ("slack"). Each step branches on the
   most constrained cell: an empty cell, or a ball/ring still waiting for its partner.
   Cell state: 0 empty, 1 full, 14/15/16 given up (empty cell / lone ball / empty ring),
   otherwise the code of the single node waiting there. */
function solve(fixed, opts = {}) {
  const limit = opts.limit || 1;
  let budget = opts.budget || 4e5;
  const st = new Uint8Array(NCELL), used = new Uint8Array(12), banned = new Uint8Array(PL.length);
  const cur = fixed.slice(), solutions = [];
  for (const p of fixed) { used[PIECE_IDS.indexOf(p.pid)] = 1;
    for (const n of p.nodes) st[n.cell] = (st[n.cell] !== 0 || n.code >= 100) ? 1 : n.code; }
  const fits = i => {
    if (used[PL_PIECE[i]] || banned[i]) return false;
    const cs = PL_CELLS[i], cd = PL_CODES[i];
    for (let k = 0; k < 3; k++) { const s = st[cs[k]];
      if (s === 0) continue;
      if (s === 1 || s >= 14 || cd[k] >= 100) return false;
      if (s < 8 ? cd[k] !== s + 6 : cd[k] !== s - 6) return false; }
    return true;
  };
  (function rec() {
    if (--budget < 0) return;
    if (cur.length === 12) { if (validateBoard(cur).solved) solutions.push(cur.slice()); return; }
    let bestC = -1, bestN = 1e9, loneBall = 0, emptyRing = 0, dead = 0;
    for (let c = 0; c < NCELL; c++) {
      const s = st[c];
      if (s === 1) continue;
      if (s === 14) { dead++; continue; } if (s === 15) { loneBall++; continue; } if (s === 16) { emptyRing++; continue; }
      let n = 0; const list = BY_CELL[c];
      for (let j = 0; j < list.length; j++) if (fits(list[j])) n++;
      if (!n) { if (s === 0) dead++; else if (s < 8) loneBall++; else emptyRing++; }
      else if (n < bestN) { bestN = n; bestC = c; }
    }
    const slack = 2 - dead - Math.max(loneBall, emptyRing);
    if (slack < 0) return;
    const cand = (bestC >= 0 ? BY_CELL[bestC] : BY_PIECE[used.indexOf(0)]).filter(fits);
    let tried = 0;
    while (tried < cand.length) {
      const i = cand[tried++], cs = PL_CELLS[i], cd = PL_CODES[i], sv = [st[cs[0]], st[cs[1]], st[cs[2]]];
      for (let k = 0; k < 3; k++) st[cs[k]] = (sv[k] !== 0 || cd[k] >= 100) ? 1 : cd[k];
      used[PL_PIECE[i]] = 1; cur.push(PL[i]);
      rec();
      cur.pop(); used[PL_PIECE[i]] = 0; for (let k = 0; k < 3; k++) st[cs[k]] = sv[k];
      banned[i] = 1; // every solution using this placement has now been explored
      if (solutions.length >= limit || budget < 0) break;
    }
    if (bestC >= 0 && solutions.length < limit && budget >= 0) { // give up on this cell; the next call re-checks the slack
      const sv = st[bestC]; st[bestC] = sv === 0 ? 14 : (sv < 8 ? 15 : 16); rec(); st[bestC] = sv;
    }
    for (let t = 0; t < tried; t++) banned[cand[t]] = 0;
  })();
  return { solutions, exhausted: budget >= 0 };
}
function samePlacement(a, b) {
  const key = p => p.nodes.map(n => n.cell * 1000 + n.code).sort((x, y) => x - y).join(',');
  return a.pid === b.pid && key(a) === key(b);
}
