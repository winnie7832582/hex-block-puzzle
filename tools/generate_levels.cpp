#include <bits/stdc++.h>
using namespace std;
struct Node{int cell,code;};
struct Pl{int pid,rot,flip,q,r; Node n[3];};
vector<Pl> all; vector<int> byCell[24], byPiece[12];
int st[24]; bool used[12]; vector<char> banned; int cur[12],depth;
long long budget; int limitS; bool shuf; mt19937 rng;
vector<array<int,12>> found;
int cellOf(int q,int r){int row=r,col=q+((r-(r&1))>>1); if(row<0||row>=4||col<0||col>=6)return -1; return row*6+col;}
inline bool fitNode(int s,int code){ if(s==0)return true; if(s==1||s>=14)return false; if(code>=100)return false; if(s<8) return code==s+6; return code==s-6; }
inline bool fits(int i){ const Pl&p=all[i]; if(used[p.pid]||banned[i])return false; for(int k=0;k<3;k++) if(!fitNode(st[p.n[k].cell],p.n[k].code))return false; return true;}
inline int after(int s,int code){ if(s!=0)return 1; if(code>=100)return 1; return code;}
bool connected(){ int par[12]; iota(par,par+12,0); function<int(int)> f=[&](int x){return par[x]==x?x:par[x]=f(par[x]);};
  int owner[24][2]; int cnt[24]={0};
  for(int i=0;i<12;i++){const Pl&p=all[cur[i]]; for(int k=0;k<3;k++){int c=p.n[k].cell; owner[c][cnt[c]++]=p.pid;}}
  for(int c=0;c<24;c++) if(cnt[c]==2) par[f(owner[c][0])]=f(owner[c][1]);
  for(int i=1;i<12;i++) if(f(i)!=f(0))return false; return true;}
void place(int i){const Pl&p=all[i]; for(int k=0;k<3;k++) st[p.n[k].cell]=after(st[p.n[k].cell],p.n[k].code); used[p.pid]=1; cur[depth++]=i;}
long long nodesUsed=0;
void rec(){
  if(--budget<0)return; nodesUsed++;
  if(depth==12){ if(connected()){array<int,12>a; copy(cur,cur+12,a.begin()); found.push_back(a);} return;}
  int bestc=-1,bestn=1e9,lb=0,er=0,e=0;
  for(int c=0;c<24;c++){ int s=st[c]; if(s==1)continue; if(s==14){e++;continue;} if(s==15){lb++;continue;} if(s==16){er++;continue;}
    int n=0; for(int i:byCell[c]) if(fits(i)){n++;}
    if(!n){ if(s==0)e++; else if(s<8)lb++; else er++; }
    else if(n<bestn){bestn=n;bestc=c;} }
  int slack=2-e-max(lb,er); if(slack<0)return;
  vector<int> cand;
  if(bestc>=0){ for(int i:byCell[bestc]) if(fits(i))cand.push_back(i);} 
  else { int pid=0; while(used[pid])pid++; for(int i:byPiece[pid]) if(fits(i))cand.push_back(i);} 
  if(shuf) shuffle(cand.begin(),cand.end(),rng);
  int tried=0;
  for(;tried<(int)cand.size();tried++){ int i=cand[tried]; const Pl&p=all[i]; int sv[3]; for(int k=0;k<3;k++)sv[k]=st[p.n[k].cell];
    place(i); rec(); depth--; used[p.pid]=0; for(int k=0;k<3;k++)st[p.n[k].cell]=sv[k]; banned[i]=1;
    if((int)found.size()>=limitS||budget<0){tried++;break;} }
  if(bestc>=0&&(int)found.size()<limitS&&budget>=0){ int sv=st[bestc]; st[bestc]= sv==0?14:(sv<8?15:16); rec(); st[bestc]=sv; }
  for(int t=0;t<tried;t++) banned[cand[t]]=0;
}
// returns number of solutions found (up to lim); -1 if budget exceeded
int run(const vector<int>&fixed,int lim,long long bud,bool sh){
  memset(st,0,sizeof st); memset(used,0,sizeof used); fill(banned.begin(),banned.end(),0); depth=0; found.clear();
  for(int i:fixed) place(i);
  budget=bud; limitS=lim; shuf=sh; rec();
  if(budget<0 && (int)found.size()<lim) return -1; return found.size();
}
int FLIPMAX=1;
int main(int argc,char**argv){ if(argc>6)FLIPMAX=atoi(argv[6]); int seed=atoi(argv[1]); rng.seed(seed); FILE*out=fopen(argv[2],"a");
  FILE*f=fopen("pieces.txt","r");
  for(int pid=0;pid<12;pid++){ int q[3],r[3],t[3],sm[3],op[3]; for(int k=0;k<3;k++) if(fscanf(f,"%d %d %d %d %d",&q[k],&r[k],&t[k],&sm[k],&op[k])!=5)return 1;
    set<vector<int>> seen;
    for(int fl=0;fl<=FLIPMAX;fl++) for(int rot=0;rot<6;rot++) for(int c=0;c<24;c++){
      int row=c/6,col=c%6; int aq=col-((row-(row&1))>>1),ar=row; Pl p; p.pid=pid;p.rot=rot;p.flip=fl;p.q=aq;p.r=ar; bool ok=true; vector<int> sig;
      for(int k=0;k<3&&ok;k++){ int x=q[k],z=r[k]; int m=sm[k],o=op[k];
        if(fl){ x=x+z; z=-z; int m2=0; for(int d=0;d<6;d++) if(m>>d&1) m2|=1<<((6-d)%6); m=m2; if(o>=0)o=(6-o)%6; }
        int y=-x-z; for(int s=0;s<rot;s++){int nx=-z,ny=-x,nz=-y;x=nx;y=ny;z=nz;}
        int m2=0; for(int d=0;d<6;d++) if(m>>d&1) m2|=1<<((d+rot)%6); if(o>=0)o=(o+rot)%6;
        int cc=cellOf(aq+x,ar+z); if(cc<0){ok=false;break;}
        int code; if(t[k]==1)code=100; else if(t[k]==0){ if(__builtin_popcount(m2)==2)code=101; else code=2+__builtin_ctz(m2);} else code=8+o;
        p.n[k]={cc,code}; sig.push_back(cc*1000+code); }
      if(!ok)continue; sort(sig.begin(),sig.end()); if(!seen.insert(sig).second)continue;
      byPiece[pid].push_back(all.size()); all.push_back(p); } }
  for(int i=0;i<(int)all.size();i++) for(int k=0;k<3;k++) byCell[all[i].n[k].cell].push_back(i);
  banned.assign(all.size(),0);
  long long SOLB=atoll(argv[3]), UNIB=atoll(argv[4]); int minK=atoi(argv[5]);
  if(minK<0){ int n=run({},1000000000,4000000000LL,false); printf("sols %d nodes %lld\n",n,nodesUsed); return 0; }
  vector<int> targets; { FILE*tf=fopen("targets.txt","r"); int v; while(fscanf(tf,"%d",&v)==1)targets.push_back(v); }
  int start=0; { FILE*rf=fopen(argv[2],"r"); int ch; while(rf&&(ch=fgetc(rf))!=EOF) if(ch=='\n')start++; }
  for(int lv=start;lv<(int)targets.size();lv++){ int K=targets[lv]; int tries=0;
    for(;;){ tries++;
      int n=run({},1,SOLB,true); if(n<1)continue;
      array<int,12> sol=found[0]; vector<int> fixed(sol.begin(),sol.end()); shuffle(fixed.begin(),fixed.end(),rng);
      vector<int> removed; bool progress=true;
      while(progress&&(int)fixed.size()>K){ progress=false;
        for(size_t j=0;j<fixed.size();j++){ vector<int> trial=fixed; trial.erase(trial.begin()+j);
          if(run(trial,2,UNIB,false)==1){ removed.push_back(fixed[j]); fixed=trial; progress=true; break; } } }
      if((int)fixed.size()!=K) continue;
      fprintf(out,"%d %d %d |",lv+1,K,tries);
      vector<int> order=fixed; for(int j=removed.size()-1;j>=0;j--)order.push_back(removed[j]);
      for(int i:order){const Pl&p=all[i]; fprintf(out," %d,%d,%d,%d,%d",p.pid,p.rot,p.flip,p.q,p.r);} fprintf(out,"\n"); fflush(out); break; } }
  return 0;
}
