#include <iostream>
#include <math.h>
#include <vector>
#include <iomanip>

using namespace std;

typedef unsigned char byte;
typedef long double TMyReal;
typedef TMyReal** Matrix;
typedef TMyReal* MyVector;

void Creatematr(Matrix* matr,int n,int m){
        TMyReal z;z=0;
        if (n) {
                (*matr)=new TMyReal*[n];
                for(int i=0;i<n;i++){
                        (*matr)[i]=new TMyReal[m];
                        for(int j=0;j<m;j++){
                                (*matr)[i][j]=z;
                        }
                }
        } else (*matr)=NULL;
}

void Destroymatr(Matrix matr,int n,int m){
        for(int i=0;i<n;i++){
				delete[] matr[i];
        }
        delete[] matr;
}

void Createvect(MyVector* vect,int n){
        TMyReal z;z=0;
		(*vect)=new TMyReal[n];
		for(int i=0;i<n;i++){
				(*vect)[i]=z;
        }
}

void Copyvect(MyVector src,MyVector cp,int n){
        for(int i=0;i<n;i++){
                cp[i]=src[i];
        }
}

class TEquationdd {
	public:
		TEquationdd(void):
		FN(10000),
		FE(2),
		Cauchy(0)
{
		Cauchy=new TMyReal[FE];
		Cauchy[0]=1;
		Cauchy[1]=0;
};
		~TEquationdd(void){
			delete [] Cauchy;
		};

		virtual void GetCauchy(MyVector c){
				for(int i=0;i<FE;i++)
						c[i]=Cauchy[i];
		}
		virtual void SetCauchy(const MyVector c){
				for(int i=0;i<FE;i++)
						Cauchy[i]=c[i];
		}

		virtual TMyReal Link(int i){
				return Cauchy[i];
		}

		virtual TMyReal GetF(int i,TMyReal Arg){
			TMyReal Result;
			switch (i) {
					case 0: Result=Link(1);  break;
					case 1: Result=(Arg*exp(-Arg)-8*Link(1)-4*Link(0))/5;
							break;
					default: Result=0;
			}
			return Result;
		}

		protected:

		int FN; //Memory size
		int FE; //Equations amount

		MyVector Cauchy;
};

//Adams Method

class TAdamsdd {
	public:

	TAdamsdd(void):
		FN(10000),FE(2),
		FMemory(0),
		FNet(0),
		FDiff(0),
		CPiece(0),
		Ya(0),
		Delta(0)
		{ };

	~TAdamsdd(void){
		delete [] FNet;
		Destroymatr(FMemory,FN,FE);
		Destroymatr(FDiff,FN,FE);
	}

	void Start(TEquationdd* FF, TMyReal Step, TMyReal Finish){

		this->FF=FF;

		FCTime=0;
		FNTime=Finish;

		Creatematr(&FDiff,FN,FE);
		Creatematr(&FMemory,FN,FE);
		Createvect(&FNet,FN);

		FCurrentStep=Step;

		Build();
	}

	MyVector GetValue(void){
		return FMemory[FS];
	}

	TMyReal** GetMemory(void){
		return FMemory;
	}

	TMyReal* GetNet(void){
		return FNet;
	}

	int GetStep(void){
		return FS;
	}

private:

    int FN,FE;
	TMyReal FCTime,FNTime,FCurrentStep;
	int FS;
	TEquationdd* FF;
	Matrix FMemory;
	MyVector FNet;
	Matrix FDiff;
	MyVector CPiece;
	Matrix Ya; //Yakobian
	MyVector Delta; //Delta

	void RungeKutta(MyVector Mem, MyVector Out){
		MyVector s1,s2,s3,s4,tmp;
		Createvect(&s1,FE);
		Createvect(&s2,FE);
		Createvect(&s3,FE);
		Createvect(&s4,FE);
		Createvect(&tmp,FE);
		CalcF(Mem,s1,FCTime);
		for (int i = 0; i < FE; i++) {
			tmp[i]=Mem[i]+s1[i]*FCurrentStep/2;
		}
		CalcF(tmp,s2,FCTime+FCurrentStep/2);
		for (int i = 0; i < FE; i++) {
			tmp[i]=Mem[i]+s2[i]*FCurrentStep/2;
		}
		CalcF(tmp,s3,FCTime+FCurrentStep/2);
		for (int i = 0; i < FE; i++) {
			tmp[i]=Mem[i]+s3[i]*FCurrentStep;
		}
		CalcF(tmp,s4,FCTime+FCurrentStep);
		for (int i = 0; i < FE; i++) {
			Out[i]=Mem[i]+(s1[i]+2*s2[i]+2*s3[i]+s4[i])*FCurrentStep/6;
		}
	}

	void Build(){
		FF->GetCauchy(FMemory[0]);
		CalcF(FMemory[0],FDiff[0], 0);
		Creatematr(&Ya,FE,FE+1);
		Createvect(&Delta,FE);
		Createvect(&CPiece,FE);
		FS=0;
		FNet[FS]=0;
		RungeKutta(FMemory[0],FMemory[1]);
		CalcF(FMemory[1],FDiff[1], FCurrentStep);
		while (FCTime<FNTime+FCurrentStep&&(FS<FN-2)){
				FF->SetCauchy(GetValue());
				FS++;
				FNet[FS]+=FCurrentStep;
				FCTime+=FCurrentStep;
				//RungeKutta(FMemory[FS],FMemory[FS+1]);
				SearchPeice();
				CalcF(FMemory[FS+1], FDiff[FS+1], FCTime+FCurrentStep);
		}
		delete [] CPiece;
		delete [] Delta;
		Destroymatr(Ya,FE,FE+1);
	}

	void CalcF(MyVector Mem, MyVector Piece, TMyReal time){
		FF->SetCauchy(Mem);
		for (int j=0;j<FE;j++) {
				TMyReal y=FF->GetF(j,time);
				Piece[j]=y;
		}
	}

	void SearchPeice(void){

		int MaxI=20;
		MyVector Arg;
        MyVector NewArg;
		MyVector tmp;

		int i,k,k1,INDEX1;
		TMyReal PrevR2,PrevR,LastR;
		TMyReal bf;
		TMyReal pow;

		Createvect(&Arg,FE);
		Createvect(&NewArg,FE);
		Createvect(&tmp,FE);

		for (int i = 0; i < FE; i++) {
			NewArg[i]=FMemory[FS][i]+(3*FDiff[FS][i]-FDiff[FS-1][i])*FCurrentStep/2;
		}
		for(i=0;i<FE;i++) Arg[i]=NewArg[i];

		k=0;
		TMyReal FEps=1.0E-10;
		LastR=1E300l;
		PrevR=1E300l;
		do {
				for(i=0;i<FE;i++) Arg[i]=NewArg[i];
				Yacobian(Arg);
				MetodNewtons(Arg,NewArg);
				k++;
				PrevR=LastR;
				LastR=0;
				for (int i = 0; i < FE; i++) {
					TMyReal r=NewArg[i]-Arg[i];
					LastR+=r*r;
				}
				LastR/=FE;
				LastR=sqrtl(LastR);
		} while (!((LastR>=PrevR)||(k>MaxI)));

		Copyvect(Arg,FMemory[FS+1],FE);

		delete [] Arg;
		delete [] NewArg;
		delete [] tmp;
	}

	void Yacobian(MyVector Arg){
		TMyReal s=1E-8l;
		TMyReal w,r;
		int f,k1,INDEX1,i,k2,INDEX2;
		TMyReal f1,f2,FD1;
		TMyReal x,y;
		for(k1=0;k1<FE;k1++){
				INDEX1=k1;
				for(k2=0;k2<FE;k2++){
						INDEX2=k2;
						r=s;

						Arg[INDEX2]=Arg[INDEX2]+r;
						f2=BigFi(Arg,INDEX1);

						Arg[INDEX2]=Arg[INDEX2]-2*r;
						f1=BigFi(Arg,INDEX1);

						Arg[INDEX2]=Arg[INDEX2]+r;

						FD1=f2;
						FD1-=f1;
						FD1/=2*r;

						Ya[INDEX1][INDEX2]=FD1;
				}
		}
	}

	TMyReal BigFi(MyVector Arg,int index){
		TMyReal f1,f2;
		CalcF(Arg,CPiece,FCTime+FCurrentStep);
		f1=FMemory[FS][index]-Arg[index];
		f2=(5*CPiece[index]+8*FDiff[FS][index]-FDiff[FS-1][index])*FCurrentStep/12;
		return -(f1+f2);
	}

	bool WithGauss(Matrix M, MyVector A, int n){
		int l;
		int bi,r,c,i;
		MyVector Temp;
		double a1,b1,sum;
		double el;
		bool Result;
		Temp=0;
		Result=false;
		l=n+1;

		for (i=0;i<n;i++){
		  bi=i;
		  for (r=i;r<n;r++)
			if (fabsl(M[r][i])>fabsl(M[bi][i])) bi=r;
			  Temp=M[bi];
			  M[bi]=M[i];
			  M[i]=Temp;
			  if (M[i][i]==0.0l) return Result;
			  el=M[i][i];
			  M[i][i]=1;
			  for(c=i+1;c<l;c++)
				if (M[i][c]==0) M[i][c]=0;
				else M[i][c]=M[i][c]/el;
			  for(r=i+1;r<n;r++){
				if (M[r][i]==0) M[r][i]=0;
				else {
				  el=M[r][i];
				  M[r][i]=0;
				  for(c=i+1;c<l;c++){
					if (M[r][c]==0) a1=0;
					else a1=M[r][c];
					if (M[i][c]==0) b1=0;
					else b1=M[i][c]*el;
					M[r][c]=a1-b1;
				  }
				}
			  }
		}

		for(i=n-1;i>=0;i--){
		  a1=0;
		  for(c=i+1;c<n;c++)
			a1=a1+M[i][c]*A[c];
		  if (a1==0) a1=0;
		  if (M[i][n]==0) A[i]=-a1;
		  else A[i]=M[i][n]-a1;
		}

		Result=true;
		return Result;
	}

	bool MetodNewtons(MyVector Arg, MyVector NewArg){

		int i,k,INDEX1,m;
		TMyReal bf;
		TMyReal sum;
		m=FE;

		for (k=0;k<FE;k++){
				INDEX1=k;
				bf=-BigFi(Arg,INDEX1);
				Ya[INDEX1][m]=bf;
		}

		bool b=WithGauss(Ya,Delta,FE);
		for(i=0;i<m;i++)
				NewArg[i]=Arg[i]+Delta[i];
		return b;
	}

};

TMyReal func(TMyReal x, int c){
	if (c==0) {
		return (sin(0.4*x)/2-cos(0.4*x))*exp(-0.8*x)+exp(-x)*(x+2);
	} else {
		return (cos(0.4*x))*exp(-0.8*x)+exp(-x)*(-x-1);
	}
}

int main (int argc, char **argv) {

	TEquationdd* e=new TEquationdd();
	TAdamsdd* a=new TAdamsdd();
	TMyReal step=0.01,finish=2;
	a->Start(e,step,finish);

	int fs=a->GetStep();

	Matrix ans=a->GetMemory();

	cout<<left<<setw(7)<<"x"<<" |" << setw(12)<<"y" << " |" << setw(12)<<"F(x)" << " |" << setw(12)<<"y'" <<" |"<< setw(12)<< "F'(x)" << endl;
	cout << "----------------------------------------------------------------" << endl;
	for (int i = 0; i < fs; i++) {
		TMyReal x=i*step,d;
		cout<<left<<setw(7)<<x<<" |";
		cout<<left<<setw(12)<<ans[i][0] << " |";
		cout<<left<<setw(12)<<func(x,0) << " |";
		d=func(x,0)-ans[i][0];
//		if (d>=0) cout<<"+";
//		cout<<d<<", ";
		cout<<left<<setw(12)<<ans[i][1] << " |";
		cout<<left<<setw(12)<<func(x,1)<< endl;
		d=func(x,0)-ans[i][0];d=func(x,1)-ans[i][1];
//		if (d>=0) cout<<"+";
//		cout<<d<<endl;
	}

	system("pause");

	return 0;
}
