#include<bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp> // Common file
#include <ext/pb_ds/tree_policy.hpp> // Including tree_order_statistics_node_update
#define int long long
#define line '\n'
#define khaled ios_base::sync_with_stdio(0);cin.tie(0);cout.tie(0);
using namespace __gnu_pbds;
using namespace std;
template<typename T>
using ordered_set=tree<T,null_type,less<T>,rb_tree_tag,tree_order_statistics_node_update>;
bool valid(long long i,long long j,long long n,long long m){return i>=0&&i<n&&j>=0&&j<m;}
long long mul(long long x,long long y,const long long&mod){return ((x%mod)*(y%mod))%mod;}
long long add(long long x,long long y,const long long&mod){return (((x%mod)+(y%mod))%mod+mod)%mod;}
long long fast_power(long long base,long long power,const long long &m=INT64_MAX){if (power == 1 || power == 0)return base * power + (!power);long long res = (fast_power(base, power / 2, m) % m) % m;if (power & 1)return mul(base,mul(res,res,m),m);else return mul(res,res,m);}
int log2_floor(long long i) {return i ? __builtin_clzll(1) - __builtin_clzll(i) : 0;}
int power_of_2(int n){ return __builtin_popcountll(n)==1;}
bool line_checking(int a1,int b1,int a2,int b2,int a3,int b3) { return (b2-b1)*(a2-a3)==(b2-b3)*(a2-a1); }
pair<int,int> rotate(int i,int j,int n){ return make_pair(j,n-1-i); }
const int N=1e6+5;
const int mod=1e9+7;
//const int mod = 998244353;
const long long inf=2e18+1;
int dx[]{1,-1,0,0,1,1,-1,-1};
int dy[]{0,0,1,-1,1,-1,1,-1};
const long double pi=3.14159265350979323846,eps=1e-8;
/*==============================================  KHALWSH  ==============================================*/
class OptimizedRoundRobin{
    int NumberOfProcesses;
    vector<int>RunningProcesses;
    vector<vector<int>>dynamicProgrammingLockUpTable;
public:
    vector<int>CurrentPathOfProcessesOfTheOptimalRoundTime;
    void InitDynamicProgrammingTable(){
        dynamicProgrammingLockUpTable.clear();
        assert(NumberOfProcesses<=22);
        vector<int>temp=RunningProcesses;
        sort(temp.rbegin(),temp.rend());
        int MaxRoundTime= accumulate(temp.begin(),temp.end(),0ll);
        dynamicProgrammingLockUpTable.resize(1<<NumberOfProcesses,vector<int>(MaxRoundTime,-1));
    }
    void init(vector<int>&Processes){
        RunningProcesses=Processes;
        NumberOfProcesses=(int)Processes.size();
        CurrentPathOfProcessesOfTheOptimalRoundTime.clear();
    }
    int GetOptimalTimeKnowingTheQuantum(int MaskOfOperationsOrder,int CurrentRoundTime=0){
        if(__builtin_popcountll(MaskOfOperationsOrder)==0)return 0;
        int &ret=dynamicProgrammingLockUpTable[MaskOfOperationsOrder][CurrentRoundTime];
        if(~ret)return ret;
        int res=inf;
        for(int i=0;i<RunningProcesses.size();i++){
            if(MaskOfOperationsOrder&(1<<i)){
                //this mean that this process isn't taken yet so i have two choices either leave it now and take it later or take it now and mark this process is taken
                res=min(res, GetOptimalTimeKnowingTheQuantum(MaskOfOperationsOrder^(1<<i),CurrentRoundTime+RunningProcesses[i])+CurrentRoundTime);
            }
        }
        return ret = res;
    }
    void BuildThePathToGetTheOptimalRoundTime(int MaskOfOperationsOrder,int CurrentRoundTime=0) {
        if (__builtin_popcountll(MaskOfOperationsOrder) == 0)return ;
        int res = inf;
        for (int i = 0; i < RunningProcesses.size(); i++) {
            if (MaskOfOperationsOrder & (1 << i)) {
                //this mean that this process isn't taken yet so i have two choices either leave it now and take it later or take it now and mark this process is taken
                if(dynamicProgrammingLockUpTable[MaskOfOperationsOrder][CurrentRoundTime]==GetOptimalTimeKnowingTheQuantum(MaskOfOperationsOrder ^ (1 << i),CurrentRoundTime + RunningProcesses[i])+CurrentRoundTime){
                    CurrentPathOfProcessesOfTheOptimalRoundTime.emplace_back(i);
                    BuildThePathToGetTheOptimalRoundTime(MaskOfOperationsOrder^(1<<i),CurrentRoundTime+RunningProcesses[i]);
                    return;
                }
            }
        }
    }
    int GetOverallWaitingTimeKnowingTheQuantumTime(int QuantumSlice){
        int res=0;
        int TotalTime=0;
        for(auto &val:CurrentPathOfProcessesOfTheOptimalRoundTime){
            TotalTime+=QuantumSlice*(RunningProcesses[val]+QuantumSlice-1)/QuantumSlice;//make ceil for the number of slice that this processes get
        }
        return TotalTime;
    }
    int GetOptimalTimeSliceAndOptimalArrangement(){
        int TernarySearchLeft=1;
        int TernarySearchRight=1e9;
        InitDynamicProgrammingTable();
        // the unit is nano second i assumed the optimal quantum is between the 1ns and 1second;
        int GetOptimalRoundTime = GetOptimalTimeKnowingTheQuantum((1<<NumberOfProcesses)-1);
        BuildThePathToGetTheOptimalRoundTime((1<<NumberOfProcesses)-1);
        int OptimalQuantumSlice=inf;
        //CurrentPathOfProcessesOfTheOptimalRoundTime--> have the index of the processes that perform the optimal path
        while(TernarySearchRight-TernarySearchLeft>3){
            int Mid1=TernarySearchLeft+(TernarySearchRight-TernarySearchLeft)/3;
            int Mid2=TernarySearchRight-(TernarySearchRight-TernarySearchLeft)/3;
            //now after getting the optimal order for the rounding time we need to build the processes
            int Mid1Ans=GetOverallWaitingTimeKnowingTheQuantumTime(Mid1);
            int Mid2Ans=GetOverallWaitingTimeKnowingTheQuantumTime(Mid2);
            if(Mid1Ans>Mid2Ans){
                //this mean the optimal quantum is at [Mid1,right]
                OptimalQuantumSlice = Mid2Ans;
                TernarySearchLeft=Mid1;
            }else if(Mid2Ans>Mid1Ans){
                OptimalQuantumSlice=Mid1Ans;  //[left,mid2]
                TernarySearchRight=Mid2;
            }else{
                //this mean the optimal in [Mid1,Mid2]
                OptimalQuantumSlice=Mid1Ans;
                TernarySearchRight=Mid2;
                TernarySearchLeft=Mid1;
            }
        }
        //bruteforcing for the remaining
        for(int i=TernarySearchLeft;i<=TernarySearchRight;i++){
            int Ans=GetOverallWaitingTimeKnowingTheQuantumTime(i);
            OptimalQuantumSlice=min(Ans,OptimalQuantumSlice);
        }
        return OptimalQuantumSlice;
    }
};
class NormalRoundRobin{
public:
    vector<int>processes;
    int QuantumSlice;
    void init(vector<int>&Running,int Slice){
        QuantumSlice=Slice;
        processes=Running;
    }
    vector<int> CalculatingResponseTimeForEveryProcesses(){
        vector<int>ResponseTime(processes.size());
        vector<int>prefix(processes);
        for(int i=1;i<processes.size();i++){
            prefix[i]+=prefix[i-1];
        }
        for(int i=0;i<processes.size();i++){
            ResponseTime[i]=prefix[i]-processes[i];
        }
        return ResponseTime;
    }
    void DisplayResponseTime(){
        vector<int>y = CalculatingResponseTimeForEveryProcesses();
        int n=(int)y.size();
        for(int i=0;i<n;i++){
            cout<<"The processes number "<<i<<" has response time = "<<y[i]<<line;
        }
    }
    vector<int> CalculatingTurnAroundTime(){
        vector<int>TurnAroundTime(processes.size());
        vector<int>temp(processes);
        int cur=0;
        while(*max_element(temp.begin(),temp.end())!=0){
            for(int i=0;i<temp.size();i++){
                cur+=(max(temp[i]-QuantumSlice,0ll)==0?temp[i]:temp[i]-QuantumSlice);
                temp[i]=max(temp[i]-QuantumSlice,0ll);
                if(temp[i]==0)
                    TurnAroundTime[i]=cur;
            }
        }
        return TurnAroundTime;
    }
    void DisplayTurnAroundTime(){
        vector<int>y = CalculatingTurnAroundTime();
        int n=(int)y.size();
        for(int i=0;i<n;i++){
            cout<<"The processes number "<<i<<" has TurnAround Time = "<<y[i]<<line;
        }
    }
};
signed main() {
    khaled
    int t;
    ::freopen("out.txt","wt",stdout);
    cin>>t;
    while(t--){
        static int TestCase=1;
        cout<<"---------------------------------------------------------------------"<<line;
        cout<<"---------------------------------------------------------------------"<<line;
        cout<<"---------------------------------------------------------------------"<<line;
        cout<<line<<line<<"This test case number "<<TestCase++<<line;
        int n=10;
        vector<int>RunningProcesses;
        for(int i=0;i<n;i++){
            int x=rand()%10;
            RunningProcesses.emplace_back(x);
        }
        while(is_sorted(RunningProcesses.begin(),RunningProcesses.end()))random_shuffle(RunningProcesses.begin(),RunningProcesses.end());
        cout<<"---------------------------------------------------------------------";
        cout<<line<<"before applying dp to get the optimal order :"<<line;
        for(auto &val:RunningProcesses){
            cout<<val<<" ";
        }
        OptimizedRoundRobin ORR;
        ORR.init(RunningProcesses);
        int OptimizedTimeSlice=ORR.GetOptimalTimeSliceAndOptimalArrangement();
        cout<<line<<"after applying dp :";
        for(auto &val:ORR.CurrentPathOfProcessesOfTheOptimalRoundTime){
            cout<<val<<" ";
        }
        cout<<line;
        //cout<<OptimizedTimeSlice<<line;
        NormalRoundRobin disp1,disp2;
        vector<int>NewProccessOrdereingByDynamicProgrammingSolution;
        for(auto &val:ORR.CurrentPathOfProcessesOfTheOptimalRoundTime){
            NewProccessOrdereingByDynamicProgrammingSolution.emplace_back(RunningProcesses[val]);
        }
        disp1.init(NewProccessOrdereingByDynamicProgrammingSolution,OptimizedTimeSlice);
        disp2.init(RunningProcesses,rand()%8);
        cout<<"optimized TimeSlice using dynamic programming"<<line;
        cout<<"--------------------------------------------------------------------------"<<line;
        cout<<"ResponseTime: "<<line;
        disp1.DisplayResponseTime();
        cout<<"TurningAroundTime "<<line;
        disp1.DisplayTurnAroundTime();
        cout<<"--------------------------------------------------------------------------"<<line;
        cout<<"normal TimeSlice using dynamic programming"<<line;
        cout<<"--------------------------------------------------------------------------"<<line;
        cout<<"ResponseTime: "<<line;
        disp2.DisplayResponseTime();
        cout<<"TurningAroundTime "<<line;
        disp2.DisplayTurnAroundTime();
    }
}
