//#pragma comment(linker, "/STACK:1024000000,1024000000")
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <limits.h>
#include <assert.h>
#include <math.h>
#include <iostream>
#include <algorithm>
#include <map>
#include <set>
#include <stack>
#include <queue>
#include <string>
#include <bitset>
#include <vector>
#include <unordered_set>
using namespace std;

#define LL long long

#define fi first
#define se second
#define lson l,mid,id<<1
#define rson mid+1,r,id<<1|1
#define ls id<<1
#define rs id<<1|1
#define MID(a,b) (((a)+(b))>>1)
#define mk(a,b) make_pair(a,b)
#define pb(a) push_back(a)
#define itr iterator
#define lowbit(x) ((x)&-(x))

typedef unsigned LL ULL;
typedef unsigned uint;
typedef map<int,int> mii;
typedef pair<int,int> pii;
typedef pair<double,double> pdd;
typedef pair<LL,LL> pLL;

template< typename T > inline void read(T &x) {
    static bool fr_f; static char fr_ch;
    fr_f=0; x=0; fr_ch=getchar();
    while(fr_ch<'0' || '9'<fr_ch) {if(fr_ch=='-') fr_f=1; fr_ch=getchar();}
    while('0'<=fr_ch && fr_ch<='9') {x=(x<<1)+(x<<3)+fr_ch-'0'; fr_ch=getchar();}
    if(fr_f) x=-x;
}

template< typename T > inline void Max (T &a, T b) {if(a<b) a=b;}
template< typename T > inline void Min (T &a, T b) {if(b<a) a=b;}
template< typename T > inline void Swap(T &a, T &b) {T c=a;a=b;b=c;}
template< typename T > inline T Abs(T a) {if(a<0) return -a; else return a;}
template< typename T > inline T maxx(const T &a, const T &b) {if(a < b) return b; return a;}
template< typename T > inline T minx(const T &a, const T &b) {if(a < b) return a; return b;}

const double   pi = (double) acos(-1.0) ;
const int     MOD = (int)1e9+7 ;
const int     INF = (int)0x3f3f3f3f ;
const LL     LINF = (LL)INF<<32|INF ;
const int    SINF = (uint)(-1)>>1 ;
const LL    SLINF = (ULL)(-1)>>1 ;
const double DINF = (double) 1e50 ;
const double  eps = (double) 1e-8 ;
const int    maxn = (int) 1e4+20 ;
const int    maxm = (int) 8e5+20 ;
const int    maxk = (int) 1000+20 ;

inline int sig(double x) {return x<-eps?-1:x>eps;}
inline LL fp(LL a,LL n,LL p) {LL res=1; for(;n;n>>=1,a=a*a%p) if(n&1) res=res*a%p; return res;}
template<typename T>inline T gcd(T a,T b) {for(T c;b;c=a%b,a=b,b=c); return a;}

//--------------------start--------------------

struct Pair
{
    int x, y;
    Pair() {}
    Pair(int _x, int _y): x(_x), y(_y) {}
};

struct Block
{
    int L, R;
    int Llen, Rlen;
    Block() {}
    Block(int _L, int _R, int _Llen, int _Rlen):
        L(_L), R(_R), Llen(_Llen), Rlen(_Rlen) {}
};

vector<int> tmp_du;
struct Graph
{
    int n;
    vector< vector<int> > init_G;
    vector< vector<bool> > G;

    vector<int> du;
    vector<int> loop;

    vector<int> rk, mp;

    void read_file(char *dir)
    {
        FILE *f = fopen(dir, "r");
        fscanf(f, "%d", &n);

        init_G = vector< vector<int> > (n);
        du = vector<int> (n);

        for(int i = 0; i < n; i++)
        {
            int num; fscanf(f, "%d", &num);
            du[i] = num;
            init_G[i] = vector<int> (num);
            for(int j = 0; j < num; j++)
            {
                int x; fscanf(f, "%d", &x);
                init_G[i][j] = x;
            }
        }

        mp = rk = vector<int> (n);
        iota(rk.begin(), rk.end(), 0);
        tmp_du = du;
        stable_sort(rk.begin(), rk.end(), [](int x, int y) {return tmp_du[x] > tmp_du[y];});

        for(int i = 0; i < n; i++) mp[rk[i]] = i;

        loop = vector<int> (n, 0);
        G = vector< vector<bool> > (n, vector<bool> (n, false));
        for(int i = 0; i < n; i++)
        {
            for(const auto j : init_G[i])
            {
                int u = mp[i], v = mp[j];
                G[u][v] = true;
                if(u == v) loop[u]++;
            }
        }

        fclose(f);
    }
};

int calc_bound(const vector<Block> &blocks)
{
    int res = 0;
    for(const auto &bk : blocks)
        res += min(bk.Llen, bk.Rlen);
    return res;
}

int find_min_value(const vector<int> &arr, int start, int len)
{
    int res = INT_MAX;
    for(int i = start; i < start + len; i++)
        if(arr[i] < res)
            res = arr[i];
    return res;
}

int find_next_min_value_index(const vector<int> &arr, int w, int start, int len)
{
    int res = -1, val = INT_MAX;
    for(int i = start; i < start + len; i++)
    {
        if(w < arr[i] && arr[i] < val)
            res = i, val = arr[i];
    }
    return res;
}

void remove_from_array(vector<int> &arr, int u, int start, int &len)
{
    int i = start;
    while(arr[i] != u) i++;
    swap(arr[i], arr[start + len - 1]);
    len--;
}

int find_min_block(const vector<Block> &blocks, const vector<int> &left)
{
    int res = -1;
    int min_size = INT_MAX;
    int min_tie_breaker = INT_MAX;

    for(int i = 0; i < (int) blocks.size(); i++)
    {
        const auto &bk = blocks[i];
        int len = max(bk.Llen, bk.Rlen);

        if(len < min_size)
        {
            len = min_size;
            res = i;
            min_tie_breaker = find_min_value(left, bk.L, bk.Llen);
        }
        else if(len == min_size)
        {
            int tie_breaker = find_min_value(left, bk.L, bk.Llen);
            if(tie_breaker < min_tie_breaker)
            {
                res = i;
                min_tie_breaker = tie_breaker;
            }
        }
    }
    return res;
}

int split(vector<int> &arr, int start, int len, const vector<bool> &adj)
{
    int slen = 0;
    for(int i = start; i < start + len; i++)
    {
        if(adj[arr[i]])
        {
            swap(arr[i], arr[start + slen]);
            slen++;
        }
    }
    return slen;
}

void rebuild_blocks(const Graph &g0, const Graph &g1,
                    const vector<Block> &blocks, int u, int v,
                    vector<int> &left, vector<int> &right, vector<Block> &res_blocks)
{
    res_blocks.reserve(blocks.size() << 1);

    for(const auto & bk : blocks)
    {
        int oldL = bk.L, oldR = bk.R, oldL_len = bk.Llen, oldR_len = bk.Rlen;
        int newL_len = split(left,  oldL, oldL_len, g0.G[u]);
        int newR_len = split(right, oldR, oldR_len, g1.G[v]);

        if(newL_len && newR_len)
        {
            res_blocks.push_back(Block(oldL, oldR, newL_len, newR_len));
        }
        if(newL_len != oldL_len && newR_len != oldR_len)
        {
            res_blocks.push_back(Block(oldL + newL_len,     oldR + newR_len,
                                       oldL_len - newL_len, oldR_len - newR_len));
        }
    }
}

int cutbranch;
void show_match_result(const Graph &g0, const Graph &g1, const vector<Pair> &result)
{
    cout <<"matching result : " <<endl;
    cout <<"result size : " <<result.size() <<endl;
    for(const auto &pr : result)
    {
        int x = g0.mp[pr.x], y = g1.mp[pr.y];
        cout <<x <<"-" <<y <<endl;
    }
//    cout <<"origin index : " <<endl;
//    for(const auto &pr : result)
//    {
//        cout <<pr.x <<"-" <<pr.y <<endl;
//    }
    cout <<"cut branch : " <<cutbranch <<endl;
    cout <<"------show message end------" <<endl;
}

void dfs(const Graph &g0, const Graph &g1,                                   //input graphs
            vector<Pair> &result, vector<Pair> &instack, int goal,           //result and goal
            vector<int> &left, vector<int> &right, vector<Block> &blocks,    //partition message
            int now_bound)                                                   //other message
{
    if(instack.size() > result.size())
    {
//        show_match_result(g0, g1, instack);
        result = instack;
    }

    now_bound = calc_bound(blocks);

    if(now_bound + (int) instack.size() < goal)
    {
        cutbranch++;
        return ;
    }

    int min_block = find_min_block(blocks, left);
    if(min_block == -1) return ;

    int u = find_min_value(left, blocks[min_block].L, blocks[min_block].Llen);
    remove_from_array(left, u, blocks[min_block].L, blocks[min_block].Llen);

    blocks[min_block].Rlen--;
    Block bk = blocks[min_block];

    if(bk.Llen == 0)
    {
        swap(blocks[min_block], blocks[blocks.size() - 1]);
        blocks.pop_back();
    }


    int v = -1, idx;
    for(int i = 0; i <= bk.Rlen; i++)
    {
        idx = find_next_min_value_index(right, v, bk.R, bk.Rlen + 1);
        v = right[idx];
        if(g0.loop[u] != g1.loop[v]) continue;

        right[idx] = right[bk.R + bk.Rlen];
        right[bk.R + bk.Rlen] = v;

        vector<Block> new_blocks;
        rebuild_blocks(g0, g1, blocks, u, v, left, right, new_blocks);

//        cout <<"i & new bk size : " <<i <<" " <<new_blocks.size() <<endl;

        instack.push_back(Pair(u, v));
        dfs(g0, g1, result, instack, goal, left, right, new_blocks, now_bound);
        instack.pop_back();
    }

    if(bk.Llen != 0) blocks[min_block].Rlen++;
    dfs(g0, g1, result, instack, goal, left, right, blocks, now_bound);
}

void preprocessing(const Graph &g0, const Graph &g1,
                   vector<Pair> &result, vector<Pair> &instack,
                   vector<int> &left, vector<int> &right, vector<Block> &blocks)
{
    cutbranch = 0;
    instack.reserve(g0.n);

    left = vector<int> (g0.n);
    iota(left.begin(), left.end(), 0);

    right = vector<int> (g1.n);
    iota(right.begin(), right.end(), 0);

    blocks.clear();
    blocks.push_back(Block(0, 0, g0.n, g1.n));
}

void MCS(const Graph &g0, const Graph &g1)
{
    vector<Pair> result, instack;
    vector<int> left, right;
    vector<Block> blocks;


    for(int goal = g0.n; goal > 0; goal--)
    {
        preprocessing(g0, g1, result, instack, left, right, blocks);
        cout <<"goal is " <<goal <<" and run search" <<endl;
        dfs(g0, g1, result, instack, goal, left, right, blocks, 0);

        cout <<"goal & result : "<<goal <<" " <<result.size() <<endl;
        if((int) result.size() >= goal)
        {
            show_match_result(g0, g1, result);
            break;
        }
    }
}


void work(int argc, char **argv)
{
//    Graph small, large;

    Graph small, large;
    if(argc >= 2)
    {
        small.read_file(argv[1]);
        large.read_file(argv[2]);
    }
    else
    {
        small.read_file("pattern");
        large.read_file("target");
    }


    if(small.n > large.n) swap(small, large);

    time_t all_st, all_ed;

    all_st = clock();
    MCS(small, large);
    all_ed = clock();

    printf("MCS run time : %.4f second\n", (double)(all_ed - all_st) / CLOCKS_PER_SEC);
}

//---------------------end---------------------

int main(int argc, char **argv)
{
    work(argc, argv);
    return 0;
}
