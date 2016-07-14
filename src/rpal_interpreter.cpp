//UFID 67431916


#include<iostream>
#include<vector>
#include<fstream>
#include<string.h>
#include<stdlib.h>
#include<sstream>
using namespace std;
 

string NT[10000];   //Array of tokens(string) used by parser
int i=0;
string c;
int j;
int size;
int size_NT;


//-----------------------------------------------------------Lexical Analyser Boolean functions-------------------------------------------------------------------------------

bool letter(char c)
{
  if((c>='a'&&c<='z')||(c>='A'&&c<='Z')||c=='_')
    return true;
  else
    return false;
}

bool digit(char c)
{
  if(c>='0'&&c<='9')
    return true;
  else
    return false;
}


bool operatr(char c){
  if(c=='+'||c=='-'||c=='*'||c=='<'||c=='>'||c=='&'||c=='.'||c=='@'||c=='/'||c==':'||c=='='||c=='~'||c=='|'||c=='$'||c=='!'||c=='#'||c=='%'||c=='^'||c=='_'||c=='['||c==']'||c=='{'||c=='}'||c=='"'||c=='?'||c==',')
    return true;
  else
    return false;
}
bool punction(char c){
  if(c=='('||c==')'||c==';'||c=='.')
    return true;
  else
    return false;
}

bool keyw(string str){
  string keywords[]={"let","and","or","fn","eq","ne","fn","in","where","within","aug","not","gr","ls","ge","le","rec","nil","true","false","dummy"};
  
  for(int i=0;i<21;i++){
    if(str==keywords[i])
      return true;
  }
    return false;
}

//------------------------------------------------Parser functions declaration------------------------------------------------------------------------------------

void nRead(string a);
void E();
void Ew();
void T();
void Ta();
void Tc();
void B();
void Bs();
void Bp();
void Bt();
void A();
void At();
void Af();
void Ap();
void R();
void Rn();
void D();
void Da();
void Dr();
void Db();
void Vb();
void Vl();
string peek();

// ---------------------------------------------------DATA STRUCTURE-------------------------------------------------------------------------------------------------

class Node{

public:
  string data;
  vector <Node> child;
  int env;
  int penv;
  int val;
  string strngVal;
  bool neg;

public:
  Node(string d)
  {
    this->neg=false;
    this->data=d;
  }

 Node(int d)
  {
    this->neg=false;
    this->val=d;
  }
  
 void attach(Node p){
   this->child.insert(this->child.begin(),p);
  }

 void display(int n){
    

     for(int j=0;j<n;j++)
       cout<<".";
     cout<<this->data<<endl;
  
     if(this->child.size()!=0)
{
     n++;
     for(int i=0;i<this->child.size();i++){
       Node K=this->child[i];
       K.display(n);
     }
   }

  }

  //STANDARDIZE EACH NODE, INCLUDED IN THE TREE DATA STRUCTURE ITSELF, WHEN THIS FUNCTION IS RUN, NODE OF TREE GETS STANDARDIZED ON WHICH IT IS CALLED

  void standardize(){

    //Standardizing rules in form of if else statement as given in tree transformation

    if(this->data=="function_form"){

      for(int i=this->child.size()-1;i>1;i--){

	Node n("lambda");
	n.child.push_back(this->child[i-1]);
	n.child.push_back(this->child[i]);
	this->child.pop_back();
	this->child.pop_back();
	this->child.push_back(n);

      }
      this->data="=";

    }

    else if(this->data=="within"){

      if(this->child[0].data=="=" && this->child[1].data=="="){
	Node X1=this->child[0];
	Node X2=this->child[1];
	this->child.clear();
	this->child.push_back(X2.child[0]);
	Node n("lambda");
	n.child.push_back(X1.child[0]);
	n.child.push_back(X2.child[1]);
	Node g("gamma");
	g.child.push_back(n);
	g.child.push_back(X1.child[1]);
	this->child.push_back(g);
	this->data="=";
      }
      else{
	cout<<"error";
      }
    }

    else if(this->data=="and"){
      Node n(",");
      Node g("tau");
      for(int i=0;i<this->child.size();i++){
	Node k=this->child[i];
	n.child.push_back(k.child[0]);
	g.child.push_back(k.child[1]);
      }
      this->child.clear();
      this->child.push_back(n);
      this->child.push_back(g);
      this->data="=";
    }

    else if(this->data=="lambda"){
      for(int i=this->child.size()-1;i>1;i--){

	Node n("lambda");
	n.child.push_back(this->child[i-1]);
	n.child.push_back(this->child[i]);
	this->child.pop_back();
	this->child.pop_back();
	this->child.push_back(n);

      }
      }

    else if(this->data=="let"){
      Node k=this->child[0];
      Node n("lambda");
      n.child.push_back(k.child[0]);
      n.child.push_back(this->child[1]);
      this->child.clear();
      this->child.push_back(n);
      this->child.push_back(k.child[1]);
      this->data="gamma";
    }

    else if(this->data=="where"){
      Node k=this->child[1];
      Node n("lambda");
      n.child.push_back(k.child[0]);
      n.child.push_back(this->child[0]);
      this->child.clear();
      this->child.push_back(n);
      this->child.push_back(k.child[1]);
      this->data="gamma";
    }

    else if(this->data=="@"){
      Node e1=this->child[0];
      Node n=this->child[1];
      Node e2=this->child[2];
      this->child.clear();
      Node g("gamma");
      g.child.push_back(n);
      g.child.push_back(e1);
      this->child.push_back(g);
      this->child.push_back(e2);
      this->data="gamma";
    }

    else if(this->data=="rec"){
      Node t=this->child[0];
      this->child.clear();
      Node l=t;
      l.data="lambda";
      Node g("gamma");
      Node y("Y");
      g.child.push_back(y);
      g.child.push_back(l);
      this->child.push_back(t.child[0]);
      this->child.push_back(g);
      this->data="=";
    }

    else{
      return;
    }

  }

  //std standardizes every node in tree by calling the standardize function repeatedly in a preorder manner

void std(){

       if(this->child.size()!=0)
       {
	 
	 for(int i=0;i<this->child.size();i++){
	   this->child[i].std();
	  }
       }
this->standardize();
}

  //===========================================PACK/UNPACK HELPER FUNCTIONS FOR CSE MACHINE=====================================================

  //used to unpack data from a given Node ie. <INT:42> becomes 42, sets the val to 42, or <STR:"42"> sets the strngVal or string value to 42

  void unpack(){
  
    if(this->data.find("<INT")==0){
      string c=this->data;
      c.erase(0,5);
      c.erase(c.end()-1);
      this->val=atoi(c.c_str());
      if(this->neg)
	this->val=0-this->val;      
    }

    else if(this->data.find("<STR")==0){
      string c=this->data;
      c.erase(0,6);
      c.erase(c.end()-1);
      c.erase(c.end()-1);
      for(int i=0;i<c.size();i++){
	if(c[i]=='\\'&&i<c.size()-1){
	  if(c[i+1]=='n'){
	    c[i]='\n';
	    c.erase(i+1,1);
	  }
	  if(c[i+1]=='t'){
	    c[i]='\t';
	    c.erase(i+1,1);
	  }
	}
      }
      this->strngVal=c;
    }
  }

  //makes a node out of the val given 2 becomes <INT:2>

  void pack(){
    stringstream ss;
    if(this->data=="<INT:"){
      ss<<this->val;
      string c=ss.str();
      this->data+=c;
      this->data+=">";
     
    }

    if(this->data=="<STR:'"){
      string c=this->strngVal;
      this->data+=c;
      this->data+="'>";
     }
  }

};



vector <Node> stck;                                                     //STACK FOR AST
vector < vector <Node> > CS;                                            //CSE CONTROL STRUCTURES
vector <Node> Q;
int num_l=0;


void BuildNode(Node p){
    stck.push_back(p);
 }
void BuildTree(Node p,int n){
     while(n>0){
      Node tmp=stck.back();
      stck.pop_back();
      p.attach(tmp);
      n--;
    }
    stck.push_back(p);
  }

void flatten(Node root);


//=============================FLATTEN AND MAKE CONTROL STRUCTURES======================================================================


void insert(vector <Node> & d, Node a){
  
  if(a.data=="lambda"){                                //handling lambda in CS
    num_l++;
    a.env=num_l;
    d.push_back(a);
    Q.push_back(a.child[1]);
    return;
  }
  else if(a.data=="->"){
    Node b("beta");
    num_l++;
    b.env=num_l;
    d.push_back(b);                                    //beta inserted with CS set to CS of first child (then clause)
    Q.push_back(a.child[1]);                           //then clause inserted in Queue with CS num of beta
    num_l++;
    Q.push_back(a.child[2]);                           //else clause inserted in Queue with CS num of beta plus one
    insert(d,a.child[0]);
  }

  else{
    d.push_back(a);
  if(a.child.size()!=0){
    for(int i=0;i<a.child.size();i++){
      insert(d,a.child[i]);
    }
  }
  }
}

void flatten(Node root){

  vector <Node> d;
  insert(d,root);
  CS.push_back(d);
}

Node print(Node k){                                                                 //<ID:Print> comes here

  if(k.data.find("<INT")==0){

    cout<<k.val;

  }
  else if(k.data=="tau"){
    cout<<"(";
    for(int i=0;i<k.child.size();i++){
      k.child[i].unpack();
      Node e=print(k.child[i]);
      if(i==k.child.size()-1)
	continue;
      else
	cout<<", ";
    }
    cout<<")";
  }
  else if(k.data=="true"||k.data=="false"||k.data=="dummy"){
    cout<<k.data;
  }
  else if(k.data=="lambda"){
    cout<<"[lambda closure: ";
    string c=k.child[0].data;
    c.erase(0,4);
    c.erase(c.end()-1);
    cout<<c<<": ";
    cout<<k.env<<"]";
  }
  else{

    cout<<k.strngVal;

  }
  Node d("dummy");
  return d;
}




//=========================================MACHINE==================================================================

void machine(){


  vector <Node> nStack;                                                              //CSE Stack
  vector <Node> nCS;                                                                 //CSE Control
  vector < vector < pair <Node, Node > > > environment(10000);                       //Environment
  vector <int> env_Stack;                                                            //To store environment values in stack to keep track of enter and exit environment
  int current=0;                                                                     //current environment
  nCS=CS[0];
  Node nprint("<ID:Print>");
  environment[0].push_back(make_pair(nprint,nprint));
  Node nconc("<ID:Conc>");
  Node nstem("<ID:Stem>");
  Node nstern("<ID:Stern>");    
  Node is1("<ID:Istuple>");
  Node is2("<ID:Isinteger>");
  Node is3("<ID:Isstring>");
  Node o("<ID:Order>");
  Node r("<ID:Istruthvalue>");
  Node q("<ID:ItoS>");
  environment[0].push_back(make_pair(q,q));
  environment[0].push_back(make_pair(is1,is1));
  environment[0].push_back(make_pair(is2,is2));
  environment[0].push_back(make_pair(is3,is3));    
  environment[0].push_back(make_pair(o,o));                                    //Primitive env, adding all this to primitive environment
  environment[0].push_back(make_pair(r,r));
  environment[0].push_back(make_pair(nconc,nconc));
  environment[0].push_back(make_pair(nstem,nstem));
  environment[0].push_back(make_pair(nstern,nstern));
  Node pe("e");
  pe.val=0;
  nStack.push_back(pe);
  env_Stack.push_back(0);

  while(nCS.size()!=0){
    Node tmp=nCS.back();
    nCS.pop_back();
    Node top=nStack.back();

    if(tmp.data=="gamma"){                                                                                      //Rule 4 gamma and lambda
      if(top.data=="lambda"){
	nStack.pop_back();
	int env=0;
	while(environment[env].size()!=0)
	  env++;

	if(top.child[0].data==","){                                      //Rule 11 n-ary functions
	  Node y=nStack.back();
	  Node x=top.child[0];

	  for(int i=0;i<x.child.size();i++){
	    pair<Node, Node> p2 (x.child[i],y.child[i]);
	    environment[env].push_back(p2);
	  }
	}
	else{                                                           //single integer
	  pair<Node,Node> p1 (top.child[0],nStack.back());
	  environment[env].push_back(p1);
	}
	nStack.pop_back();

	environment[env].insert(environment[env].end(),environment[top.penv].begin(),environment[top.penv].end()); //copying parent environments values
	current=env;
	Node e("e"); //environment marker
	e.val=env;
	env_Stack.push_back(env);
	nStack.push_back(e);
	nCS.push_back(e);
	nCS.insert(nCS.end(),CS[top.env].begin(),CS[top.env].end()); //loading new control structure
      }

      //======================================GAMMA OPERATORS=================================================================================
      else if(top.data=="<ID:Print>"){                                     //primitive environment

	nStack.pop_back();
	Node d=print(nStack.back());
	nStack.pop_back();
	nStack.push_back(d);
      }

      else if(top.data=="<ID:ItoS>"){                                     //primitive environment
	nStack.pop_back();
	nStack.back().data="<STR:'";
	stringstream sa;
	sa<<nStack.back().val;
	nStack.back().strngVal=sa.str();
	nStack.back().pack();
	nStack.back().val=0;
   
      }

      else if(top.data=="<ID:Conc>"){                                    //primitive environment and so on
	nStack.pop_back();
	string x=nStack.back().strngVal;
	nStack.pop_back();
	string y=nStack.back().strngVal;
	nStack.pop_back();	
	string z=x+y;
	Node z1("<STR:'");
	z1.strngVal=z;
	z1.pack();
	nStack.push_back(z1);
      }

      else if(top.data=="<ID:Istuple>"){
	nStack.pop_back();
	if(nStack.back().data=="tau"||nStack.back().data=="nil"||nStack.back().data=="<nil>"){
	  nStack.pop_back();
	  Node t("true");
	  nStack.push_back(t);
	}
	else{
	  nStack.pop_back();
	  Node f("false");
	  nStack.push_back(f);
	}
      }

      else if(top.data=="<ID:Isstring>"){
	nStack.pop_back();
	if(nStack.back().data.find("<STR")==0){
	  nStack.pop_back();
	  Node t("true");
	  nStack.push_back(t);
	}
	else{
	  nStack.pop_back();
	  Node f("false");
	  nStack.push_back(f);
	}
      }

      else if(top.data=="<ID:Istruthvalue>"){
	nStack.pop_back();
	if(nStack.back().data=="true"||nStack.back().data=="<true>"||nStack.back().data=="false"||nStack.back().data=="<false>"){
	  nStack.pop_back();
	  Node t("true");
	  nStack.push_back(t);
	}
	else{
	  nStack.pop_back();
	  Node f("false");
	  nStack.push_back(f);
	}
      }

     else if(top.data=="<ID:Isinteger>"){
	nStack.pop_back();
	if(nStack.back().data.find("<INT")==0){
	  nStack.pop_back();
	  Node t("true");
	  nStack.push_back(t);
	}
	else{
	  nStack.pop_back();
	  Node f("false");
	  nStack.push_back(f);
	}
      }

     else if(top.data=="<ID:Order>"){
       nStack.pop_back();
       int k=nStack.back().child.size();
       Node s("<INT:");
       s.val=k;
       s.pack();
       nStack.pop_back();
       nStack.push_back(s);
     }


      else if(top.data=="<ID:Stem>"){
	nStack.pop_back();
	string x=nStack.back().strngVal;
	nStack.pop_back();
	x.erase(1,x.size());
	Node x1("<STR:'");
	x1.strngVal=x;
	x1.pack();
	nStack.push_back(x1);
      }

      else if(top.data=="<ID:Stern>"){
	nStack.pop_back();
	string x=nStack.back().strngVal;
	nStack.pop_back();
	x.erase(x.begin());
	Node x1("<STR:'");
	x1.strngVal=x;
	x1.pack();
	nStack.push_back(x1);
      }

      else if(top.data=="tau"){                                                                                //Rule 10 tuple selection
	nStack.pop_back();
	int a=nStack.back().val;
	Node k=top.child[a-1];
	nStack.pop_back();
	nStack.push_back(k);
      }

      else if(top.data=="Y"){                                                                                   //Rule 12 recursion
	Node k("rho");
	nStack.pop_back();
	k.child.push_back(nStack.back());
	nStack.pop_back();
	nStack.push_back(k);
      }

      else if(top.data=="rho"){                                                                                 //Rule 13 recursion
	nStack.push_back(top.child[0]);
	nCS.push_back(tmp);
	Node k("gamma");
	nCS.push_back(k);
      }
    }

    else if(tmp.data=="lambda"){                                                                                 //Rule 2 pushing lambda
      tmp.penv=current;
      nStack.push_back(tmp);
    }

    else if(tmp.data.find("ID")==1){                                                                             //Rule 1 search environment and put values
      vector <pair <Node, Node> > v1=environment[current];
      for(int i=0;i<v1.size();i++){
	if(tmp.data==v1[i].first.data){
	  v1[i].second.unpack();
	  nStack.push_back(v1[i].second);
	    break;
	}
      }

    }

    else if(tmp.data=="e"){                                                                                        //Rule 5 exit environment
      nStack.pop_back();
      if(nStack.back().data=="e"&&nStack.back().val==tmp.val){
	nStack.pop_back();
	nStack.push_back(top);
	env_Stack.pop_back();
	current=env_Stack.back();
      }
    }

    //==============================OPERATORS=======================================================================================
    //Rule 7

    else if(tmp.data=="+"){
      
      int a=top.val;
     
      nStack.pop_back();
      int b=nStack.back().val;
     
      nStack.pop_back();
      int d=a+b;
     
      Node q("<INT:");
      q.val=d;
      q.pack();
      nStack.push_back(q);
    }

    else if(tmp.data=="/"){
      
      int a=top.val;
     
      nStack.pop_back();
      int b=nStack.back().val;
     
      nStack.pop_back();
      int d=a/b;
     
      Node q("<INT:");
      q.val=d;
      q.pack();
      nStack.push_back(q);
    }

    else if(tmp.data=="-"){
      
      int a=top.val;
     
      nStack.pop_back();
      int b=nStack.back().val;
     
      nStack.pop_back();
      int d=a-b;
     
      Node q("<INT:");
      q.val=d;
      q.pack();
      nStack.push_back(q);
    }

    else if(tmp.data=="*"){
      
      int a=top.val;
     
      nStack.pop_back();
      int b=nStack.back().val;
     
      nStack.pop_back();
      int d=a*b;
     
      Node q("<INT:");
      q.val=d;
      q.pack();
      nStack.push_back(q);
    }

    //=============================================BOOLEAN OPS============================================================

    else if(tmp.data=="<"||tmp.data=="ls"){
      if(top.data.find("<INT")==0){
	int a=top.val;
	nStack.pop_back();
	int b=nStack.back().val;
	nStack.pop_back();
	if(a<b){
	  Node b("true");
	  nStack.push_back(b);
	}
	else{
	  Node b("false");
	  nStack.push_back(b);
	}
      }
      else{
	string a=top.strngVal;
	nStack.pop_back();
	string b=nStack.back().strngVal;
	nStack.pop_back();
	if(a<b){
	  Node b("true");
	  nStack.push_back(b);
	}
	else{
	  Node b("false");
	  nStack.push_back(b);
	}
      }
    }


    else if(tmp.data==">"||tmp.data=="gr"){
      if(top.data.find("<INT")==0){
	int a=top.val;
	nStack.pop_back();
	int b=nStack.back().val;
	nStack.pop_back();
	if(a>b){
	  Node b("true");
	  nStack.push_back(b);
	}
	else{
	  Node b("false");
	  nStack.push_back(b);
	}
      }
      else{
	string a=top.strngVal;
	nStack.pop_back();
	string b=nStack.back().strngVal;
	nStack.pop_back();
	if(a>b){
	  Node b("true");
	  nStack.push_back(b);
	}
	else{
	  Node b("false");
	  nStack.push_back(b);
	}
      }
    }


    else if(tmp.data=="<="||tmp.data=="le"){
      if(top.data.find("<INT")==0){
	int a=top.val;
	nStack.pop_back();
	int b=nStack.back().val;
	nStack.pop_back();
	if(a<=b){
	  Node b("true");
	  nStack.push_back(b);
	}
	else{
	  Node b("false");
	  nStack.push_back(b);
	}
      }
      else{
	string a=top.strngVal;
	nStack.pop_back();
	string b=nStack.back().strngVal;
	nStack.pop_back();
	if(a<=b){
	  Node b("true");
	  nStack.push_back(b);
	}
	else{
	  Node b("false");
	  nStack.push_back(b);
	}
      }
    }


    else if(tmp.data==">="||tmp.data=="ge"){
      if(top.data.find("<INT")==0){
	int a=top.val;
	nStack.pop_back();
	int b=nStack.back().val;
	nStack.pop_back();
	if(a>=b){
	  Node b("true");
	  nStack.push_back(b);
	}
	else{
	  Node b("false");
	  nStack.push_back(b);
	}
      }
      else{
	string a=top.strngVal;
	nStack.pop_back();
	string b=nStack.back().strngVal;
	nStack.pop_back();
	if(a>=b){
	  Node b("true");
	  nStack.push_back(b);
	}
	else{
	  Node b("false");
	  nStack.push_back(b);
	}
      }
    }


    else if(tmp.data=="eq"){
      if(top.data.find("<INT")==0){
	int a=top.val;
	nStack.pop_back();
	int b=nStack.back().val;
	nStack.pop_back();
	if(a==b){
	  Node b("true");
	  nStack.push_back(b);
	}
	else{
	  Node b("false");
	  nStack.push_back(b);
	}
      }
      else{
	string a=top.strngVal;
	nStack.pop_back();
	string b=nStack.back().strngVal;
	nStack.pop_back();
	if(a==b){
	  Node b("true");
	  nStack.push_back(b);
	}
	else{
	  Node b("false");
	  nStack.push_back(b);
	}
      }
    }


    else if(tmp.data=="ne"){
      if(top.data.find("<INT")==0){
	int a=top.val;
	nStack.pop_back();
	int b=nStack.back().val;
	nStack.pop_back();
	if(a!=b){
	  Node b("true");
	  nStack.push_back(b);
	}
	else{
	  Node b("false");
	  nStack.push_back(b);
	}
      }
      else{
	string a=top.strngVal;
	nStack.pop_back();
	string b=nStack.back().strngVal;
	nStack.pop_back();
	if(a!=b){
	  Node b("true");
	  nStack.push_back(b);
	}
	else{
	  Node b("false");
	  nStack.push_back(b);
	}
      }
    }

    else if(tmp.data=="&"){
      nStack.pop_back();
      if(top.data=="true"&&nStack.back().data=="true"){
	Node b("true");
	nStack.pop_back();
	nStack.push_back(b);
      }
      else{
	Node b("false");
	nStack.pop_back();
	nStack.push_back(b);
      }
    }

    else if(tmp.data=="or"){
      nStack.pop_back();
      if(top.data=="false"&&nStack.back().data=="false"){
	Node b("false");
	nStack.pop_back();
	nStack.push_back(b);
      }
      else{
	Node b("true");
	nStack.pop_back();
	nStack.push_back(b);
      }
    }

    else if(tmp.data=="aug"){
      nStack.pop_back();
      if(top.data=="nil"||top.data=="<nil>"){
	Node t("tau");
	t.child.push_back(nStack.back());
	nStack.pop_back();
	nStack.push_back(t);
      }
      else{
	top.child.push_back(nStack.back());
	nStack.pop_back();
	nStack.push_back(top);
      }
    }

    //==============================================UNARY OPS====================================================
    //Rule 6
    else if(tmp.data=="neg"){
      nStack.back().neg=true;
      nStack.back().unpack();
    }

    else if(tmp.data=="not"){
      if(top.data=="true"||top.data=="<true>")
	nStack.back().data="false";
      else
	nStack.back().data="true";
    }
    
    //======================================================================================OPERANDS==================================
    else if(tmp.data.find("INT")==1){
      tmp.unpack();
      nStack.push_back(tmp);
    }

    else if(tmp.data.find("STR")==1){
      tmp.unpack();
      nStack.push_back(tmp);
    }

    //=============================================BETA/RELATIONAL OPS=================================================================
    else if(tmp.data=="beta"){                                                  //Rule 8 Conditional
      nStack.pop_back();
      if(top.data=="true")
	nCS.insert(nCS.end(),CS[tmp.env].begin(),CS[tmp.env].end());            //loading new control structure (then clause)
      else
	nCS.insert(nCS.end(),CS[tmp.env+1].begin(),CS[tmp.env+1].end());        //loading new control structure (else clause)
    }
    
    //================================================================================================================================

    else if(tmp.data=="tau"){                                                  //Rule 9 tuple formation
      for(int i=0;i<tmp.child.size();i++){

	tmp.child[i]=nStack.back();
	nStack.pop_back();
      }
      nStack.push_back(tmp);
      }

     else if(tmp.data=="<true>"){
       Node t("true");
       nStack.push_back(t);
     }
     else if(tmp.data=="<false>"){
       Node t("false");
       nStack.push_back(t);
     }
     else if(tmp.data=="<dummy>"){
       Node t("dummy");
       nStack.push_back(t);
     }
    else{
      nStack.push_back(tmp);
    }
  }

}




//=============================================================MACHINE OVER====================================================================================














//--------------------------------------------------------Parser Grammar functions----------------------------------------------------------------------------------------------

//# EXPRESSIONS ###############################################################################################

void E(){

int n=0;
if(NT[i]=="let"){
nRead("let");
D();
nRead("in");
E();
Node K("let");
BuildTree(K,2);
}
else if(NT[i]=="fn"){
nRead("fn");
do{
Vb();
n++;
 }while(NT[i].find("ID")==0||NT[i]=="(");
nRead(".");
E();
Node L("lambda");
BuildTree(L,n+1);
}
else{
Ew();
}
}

void Ew()
{

T();
if(NT[i]=="where"){
nRead("where");
Dr();
Node K("where");
BuildTree(K,2);
}
}

//## TUPLE EXPRESSIONS ######################################################################

void T(){

Ta();
if(NT[i]==","){
  int n=0;
  do{
    nRead(",");
     Ta();
     n++;
  }while(NT[i]==",");
Node K("tau");
BuildTree(K,n+1);
}
}

void Ta(){

Tc();
while(NT[i]=="aug"){
nRead("aug");
Tc();
Node K("aug");
BuildTree(K,2);
}
}

void Tc(){

B();
if(NT[i]=="->"){
nRead("->");
Tc();
nRead("|");
Tc();
Node L("->");
BuildTree(L,3);
}
}

//# BOOLEAN EXPRESSIONS #############################################################################

void B(){

Bt();
while(NT[i]=="or"){
nRead("or");
Bt();
Node O("or");
BuildTree(O,2);
}
}

void Bt(){

Bs();
while(NT[i]=="&"){
nRead("&");
Bs();
Node S("&");
BuildTree(S,2);
}
}

void Bs(){

if(NT[i]=="not"){
nRead("not");
Bp();
Node B("not");
BuildTree(B,1);
}
else{
Bp();
}
}

void Bp(){

A();
if(NT[i]=="gr"||NT[i]==">"||NT[i]=="ge"||NT[i]==">="||NT[i]=="ls"||NT[i]=="<"||NT[i]=="le"||NT[i]=="<="||NT[i]=="eq"||NT[i]=="ne"){
  string tmp=NT[i];
nRead(tmp);
A();
Node B(tmp);
BuildTree(B,2);
}
}

//# ARITHMETIC EXPRESSIONS ###############################################################################

void A(){
  if(NT[i]=="-"){
    nRead("-");
    At();
    Node K("neg");
    BuildTree(K,1);
  }
  else if(NT[i]=="+"){
    nRead("+");
    At();
  }
  else
    {
      At();
    }
  while(NT[i]=="+"||NT[i]=="-"){
    string tmp=NT[i];
    nRead(tmp);
    At();
    Node L(tmp);
    BuildTree(L,2);
  }
}

void At(){

Af();
while(NT[i]=="*"||NT[i]=="/"){
  string tmp=NT[i];
nRead(tmp);
Af();
Node K(tmp);
BuildTree(K,2);
}
}

void Af(){

Ap();
if(NT[i]=="**"){
nRead("**");
Af();
Node K("**");
BuildTree(K,2);
}
}

void Ap(){
R();
while(NT[i]=="@"){
nRead("@");
nRead("ID");
R();
Node K("@");
BuildTree(K,3);
}
}

//# RATORS AND RANDS ##############################################################################

void R(){


Rn();
 while(NT[i].find("ID")==0||NT[i].find("INT")==0||NT[i].find("STR")==0||NT[i]=="true"||NT[i]=="false"||NT[i]=="nil"||NT[i]=="("||NT[i]=="dummy"){
Rn();
Node K("gamma");
BuildTree(K,2);
}
}

void Rn(){

  if(NT[i].find("ID")==0){
  nRead("ID");
}
  else if(NT[i].find("INT")==0){
nRead("INT");
}
  else if(NT[i].find("STR")==0){
nRead("STR");
}
else if(NT[i]=="true"){
nRead("true");
}
else if(NT[i]=="false"){
nRead("false");
}
else if(NT[i]=="nil"){
nRead("nil");
}
else if(NT[i]=="("){
nRead("(");
E();
nRead(")");
}
else if(NT[i]=="dummy"){
nRead("dummy");
}
 else{
   return;
 }
}
//# DEFINITIONS ##############################################################################

void D(){

Da();
if(NT[i]=="within"){
nRead("within");
D();
Node K("within");
BuildTree(K,2);
}
}

void Da(){
Dr();
if(NT[i]=="and"){
  int n=0;
  do{
    nRead("and");
    Dr();
    n++;
  }while(NT[i]=="and");
Node K("and");
BuildTree(K,n+1);
}
return;
}

void Dr(){
if(NT[i]=="rec"){
nRead("rec");
Db();
Node K("rec");
BuildTree(K,1);
}
else{
Db();
 }
}

void Db(){
  if(NT[i]=="("){
    nRead("(");
    D();
    nRead(")");
  }
  else if(NT[i].find("ID")==0){
    string NN=peek();
    if(NN==","||NN=="="){
      Vl();
      nRead("=");
      E();
      Node K("=");
      BuildTree(K,2);
    }
    else{
      nRead("ID");
      int n=0;
      do{
	Vb();
	n++;
      }while(NT[i].find("ID")==0||NT[i]=="(");
      nRead("=");
      E();
      Node L("function_form");
      BuildTree(L,n+2);
    }
  }
  else{
    return;
  }
}

//# VARIABLES ########################################################################

void Vb(){

if(NT[i].find("ID")==0){
nRead("ID");
}
else if(NT[i]=="("){
  nRead("(");
  if(NT[i]==")"){
    nRead(")");
    Node K("()");
    BuildNode(K);
  }
  else{
    Vl();
    nRead(")");
  }
 }
}

void Vl(){

nRead("ID");
if(NT[i]==","){
int n=0;
do{
nRead(",");
nRead("ID");
n++;
 }while(NT[i]==",");
Node K(",");
BuildTree(K,n+1);
}
}

//---------------------------Read and Peek----------------------------------------------------


void nRead(string a){

  if(NT[i]==a||NT[i].find(a)==0){

    if(a=="ID"||a=="INT"||a=="STR"||a=="true"||a=="false"||a=="nil"||a=="dummy")
      {
	NT[i]+=">";
	NT[i]="<"+NT[i];
	Node K(NT[i]);
	BuildNode(K);
      }
    i++;

  }
  else{
    cout<<"Error: Expected Token "<<a<<" found "<<NT[i];
    exit (EXIT_FAILURE);
  }
}


string peek(){

  return NT[i+1];
}
 

//--------------------------------------------------Main (file Open) (lexical analysis)--------------------------------------------------------------------------


int main(int argc, char* argv[])
{
  bool ast=false;
  bool l=false;  
  for(int k=0;k<argc;k++){
    string g=argv[k];
    if(g=="-l")
      l=true;
    if(g=="-ast")
      ast=true;
  }

//========================================L case================================================


  ifstream fin;
  fin.open(argv[argc-1]);
  j=0;
  c.reserve(10000);
  while(fin.get(c[j])){
    j++;
  }
  //File to string c
  size=j;
  j=0;
  i=0;
  string token;
  char d;

  //lexical analyser on the string c
  //automata in while loop over string c
  //tokens passed to array NT, array of tokens, used by parser 
  while(j<size)
    {
      d=c[j+1];
      if(letter(c[j])){
	token=c[j];
	j++;
	while(letter(c[j])||digit(c[j])){
	  token+=c[j];
	  j++;
	}
	
	if(keyw(token)){
	  NT[i]=token;
	  i++;
	}
	else{
	token="ID:"+token;
	NT[i]=token;
	i++;
	}
	token='\0';
      }
      else if(digit(c[j])){
	token=c[j];
	j++;
	while(digit(c[j])){
	  token+=c[j];
	  j++;
	}
	token="INT:"+token;
	NT[i]=token;
	i++;
	token='\0';
      }
      else if(c[j]=='/'&&d=='/'){
	do{
	  j++;
	}while((int)c[j]!=10);
      }
      else if(operatr(c[j])||punction(c[j])){
	if(c[j]=='-'&&d=='>'){
	  token=c[j];
	  token+=d;
	  NT[i]=token;
	  i++;
	  token='\0';
	  j+=2;
	}
	else if(c[j]=='*'&&d=='*'){
	  token=c[j];
	  token+=d;
	  NT[i]=token;
	  i++;
	  token='\0';
	  j=j+2;
	}
	else if(c[j]=='>'&&d=='='){
	  token=c[j];
	  token+=d;
	  NT[i]=token;
	  i++;
	  token='\0';
	  j+=2;
	}
	else if(c[j]=='<'&&d=='='){
	  token=c[j];
	  token+=d;
	  NT[i]=token;
	  i++;
	  token='\0';
	  j+=2;
	}    
	else{
	  token=c[j];
	  NT[i]=token;
	  i++;
	  token='\0';
	  j++;
	}
      }
      else if(c[j]=='\''){
	token=c[j];
	j++;
	while(c[j]!='\''){
	  token+=c[j];
	  j++;
	}
	token+=c[j];
	token="STR:"+token;
	NT[i]=token;
	i++;
	token='\0';
	j++;
      }
      
      else if((c[j]==' ')||((int)c[j]==10)||((int)c[j]==9)){
	j++;
      }
      else{
	cout<<"error";
	j++;
      }
    }
  fin.close();


 //====================================================================FILE READ and converted to tokens===================================================================
 if(l){
  size_NT=i;
      for(int a=0;a<size_NT;a++){
      cout<<NT[a]<<endl;
    }
  }

 //parsing-----------------------------------------------------------------------------------------------------

 i=0;
 E();//start  

 //==========================PARSED :- AST in stck.back()===========================================

 if(ast){
   stck.back().display(0);//display tree
 }

 //=============================STANDARDIZE============================================

 stck.back().std();
 //========================CNTRL STRUCT====================================

 Q.push_back(stck.back());
 while(Q.size()!=0){
   flatten(Q.front());
   Q.erase(Q.begin());
 }
 //============================MACHINE======================================
 machine();
 cout<<"\n";
 return 0;
}
