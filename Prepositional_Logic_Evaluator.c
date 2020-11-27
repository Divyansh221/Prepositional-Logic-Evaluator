// Prepositional-Logic-Evaluator 

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX 10000

/**********************************************************/
/************** Stack Datatype and Operations *************/
/**********************************************************/

// stack structure declaration
typedef struct stackADT {
    char opr[MAX];
    int top;
} Stack;

// initialize stack
void initStack (Stack *stack)
{
    stack->top = -1;
}

// check whether stack is empty
int isEmptyStack (Stack *stack)
{
    return (stack->top == -1);
}

// check whether stack is full
int isFullStack (Stack *stack)
{
    return (stack->top == MAX-1);
}

// push an element into stack
void push (Stack *stack, char x)
{
    if (isFullStack(stack))
        printf("Error: Stack is Full!\n");
    else
        stack->opr[++(stack->top)] = x;
}

// pop an element from stack
char pop (Stack *stack)
{
    char x;
    if (isEmptyStack(stack))
        printf("Error: Stack is Empty!\n");
    else
        x = stack->opr[(stack->top)--];
    return x;
}

/**********************************************************/


/**********************************************************/
/*********** Binary Tree Datatype and Operations **********/
/**********************************************************/

// binary tree structure declaration
typedef struct binTree {
    char element;
    struct binTree *leftChild;
    struct binTree *rightChild;
} BT;

// creating a node in binary tree
BT *createNode (char el)
{
    BT *newNode;
    if ( (newNode=(BT *)malloc(sizeof(BT))) == NULL )
        printf("Error: Malloc Error in Creating Node!\n");
    else {
        newNode->element = el;
        newNode->leftChild = NULL;
        newNode->rightChild = NULL;
    }
    return (newNode);
}

// creating an exact replica of the the binary tree
BT *duplicate(BT *orig)
{
    BT *dup = NULL;
    if(orig != NULL) {
        dup = createNode(orig->element);
        dup->leftChild = duplicate(orig->leftChild);
        dup->rightChild = duplicate(orig->rightChild);
    }
    return (dup);
}

/**********************************************************/


/**********************************************************/
/******************** Utility Functions *******************/
/**********************************************************/

// structure holding propositional values
typedef struct PropVal {
    char prop;
    int val; // '0' for False and '1' for True
} PV;

// scan every propositional values (one by one) from user as input
PV *scanPropValueInput()
{
    unsigned int noProp, i;
    PV *pvarr;
    
    printf("Enter Total Number of Propositions: ");
    scanf("%u",&noProp);
    
    pvarr = (PV *)malloc(noProp * sizeof(PV));
    
    for (i = 0; i < noProp; i++) {
        printf("Enter Proposition [%u] (Format: Name <SPACE> Value): ", i+1);
        scanf(" %c %d", &pvarr[i].prop, &pvarr[i].val);
    }
    return pvarr;
}

// determines whether p is a proposition including 0 or 1
int isProposition (char p)
{
    return ( ((p >= 'a') && (p <= 'z')) || ((p >= 'A') && (p <= 'Z')) || (p == '0') || (p == '1') );
}

// printing the validity and satisfiability flags
void printResult (int valid, int sat)
{
    printf("\nThe Given Formula is: < ");
    valid ? printf("VALID") : printf("INVALID");
    printf(" + ");
    sat ? printf("SATISFIABLE") : printf("UNSATISFIABLE");
    printf(" >\n\n");
}

//display postfix form of propositional formula (from internally represented string)
void displayPfForm(char *pfForm)
{
    int i;
    
    printf("Postfix Representation of Formula:");
    for(i = 0; pfForm[i] != '\0'; i++){
        if ( pfForm[i] == '-' )
            printf(" ->");
        else if (pfForm[i] == '~')
            printf(" <->");
        else
            printf(" %c", pfForm[i]);
    }
    printf("\n");
}

// count number of characters in the formula representing only propositions and operators
int noOfIdsInFormula (char *formula)
{
    int i, len = strlen(formula), count = 0;
    for(i = 0; i < len; i++){
        if ( (formula[i] != '(') && (formula[i] != ')') && (formula[i] != ' ') && (formula[i] != '\t') )
            count++;
    }
    return count;
}

// pre-defined priority of in-stack element
int inStackPriority (char op){
    switch(op){
        case '!': return 3; break;
        
        case '&':
        case '|': return 2; break;
        
        case '~':
        case '-': return 1; break;
        
        case '(': return 0; break;
        
        default : return -1; break;
    }
}

// pre-defined priority of in-coming element
int inComingPriority (char op){
    switch(op){
        case '!': return 4; break;
        
        case '&':
        case '|': return 2; break;
        
        case '~':
        case '-': return 1; break;
        
        case '(': return 4; break;
        
        default : return -1; break;
    }
}

// generate postfix formula from the given input formula
char *genPostFixFormula(char *formula)
{
    int noOfIds = noOfIdsInFormula(formula), i, len = strlen(formula), k;
    char *pf = (char *)malloc((noOfIds+1) * sizeof(char));
    char out;
    Stack *stack = (Stack *)malloc(sizeof(Stack));
    initStack(stack); push(stack,'#');
    
    for (i = 0, k = 0; i < len; i++){
        if ( (formula[i] != ' ') && (formula[i] != '\t') ){
            if ( isProposition(formula[i]) )
                pf[k++] = formula[i];
            else if (formula[i] == ')') {
                while ( (out = pop(stack)) != '(')
                    pf[k++] = out;
            }
            else {
                while ( inStackPriority(out = pop(stack)) >= inComingPriority(formula[i]) )
                    pf[k++] = out;
                push(stack, out);
                push(stack, formula[i]);
            }
        }
    }
    while( (out = pop(stack)) != '#' )
        pf[k++] = out;
    pf[k] = '\0';
    
    return pf;
}

/**********************************************************/





/**********************************************************/
/****************** YOUR CODE STARTS HERE *****************/
/**********************************************************/

//expression tree formation from postfix formula string
BT *ETF (char *pfForm, int start, int end)
{
    BT *et = NULL;
    if(end-start+1 == 1) et = createNode(pfForm[end]);
    if(end-start+1 > 1 && pfForm[end] == '!'){
        et = createNode('!');
        et->leftChild = NULL;
        et->rightChild = ETF(pfForm, start, end-1);
    }
    if(end-start+1 > 2 && ( pfForm[end] == '&' || pfForm[end] == '|' || pfForm[end] == '-' || pfForm[end] == '~' )){
        et = createNode(pfForm[end]);
        int x = 0, y = 0;
        int k = -1;
        for (int i = start; i < end; ++i){
            if(isProposition(pfForm[i])) x++;
            else if(pfForm[i] != '!'){
                y++;
                if(x-y == 1){
                    k = i;
                }
            }
        }
        if(k == -1){
            if(pfForm[start+1] == '!') k = start+1;
            else k = start;
        }
        et->leftChild = ETF(pfForm, start, k);
        et->rightChild = ETF(pfForm, k+1, end-1);
    }
    return et;
}

// // printing the expresion tree using inorder traversal
void ETP (BT *et)
{
    if(et != NULL){
        if(et->element != '!' && !isProposition(et->element)) printf(" (");
        ETP(et->leftChild);
        if ( et->element == '-' )
            printf(" ->");
        else if (et->element == '~')
            printf(" <->");
        else
            printf(" %c", et->element);
        ETP(et->rightChild);
        if(et->element != '!' && !isProposition(et->element)) printf(" )");
    }
}

// // evaluate the formula from the expression tree from the proposition values provided in varr[] array
int EVAL (BT *et, PV *pvarr)
{
    int result;
    
    if(isProposition(et->element)){
        int key;
        for (int i = 0; i < sizeof(pvarr); ++i){
            if(pvarr[i].prop == et->element) key = pvarr[i].val;
        }
        result = (key == 1)?1:0;
    } 
    if(et->element == '!') result = (EVAL(et->rightChild, pvarr) == 1)?0:1;
    if(et->element == '&') result = (EVAL(et->rightChild, pvarr)) && (EVAL(et->leftChild, pvarr));
    if(et->element == '|') result = (EVAL(et->rightChild, pvarr)) || (EVAL(et->leftChild, pvarr));
    if(et->element == '-') result = ((EVAL(et->rightChild, pvarr) == 0) && (EVAL(et->leftChild, pvarr) == 1))?0:1;
    if(et->element == '~') result = (((EVAL(et->rightChild, pvarr) == 1) && (EVAL(et->leftChild, pvarr) == 1)) || ((EVAL(et->rightChild, pvarr) == 0) && (EVAL(et->leftChild, pvarr) == 0)))?1:0;
    return result;
}

// // convert expression tree to IFF expression tree
BT *IFF (BT *et)
{
    if(et->element == '!') et->rightChild = IFF(et->rightChild);
    else if(et->element == '&' || et->element == '|'){
        et->leftChild = IFF(et->leftChild);
        et->rightChild = IFF(et->rightChild);
    }
    else if(et->element == '-'){
        et->element = '|';
        BT *temp1, *temp2;
        temp1 = et->leftChild;
        et->leftChild = createNode('!');
        temp2 = et->leftChild;
        temp2->rightChild = temp1;
        temp2->rightChild = IFF(temp2->rightChild);
        et->rightChild = IFF(et->rightChild);
    }
    else if(et->element == '~'){
        et->element = '-';
        BT *x, *y;
        x = duplicate(et);
        y = duplicate(et);
        BT *temp;
        temp = y->leftChild;
        y->leftChild = y->rightChild;
        y->rightChild = temp;
        et->element = '&';
        et->leftChild = x;
        et->rightChild = y;
        et->leftChild = IFF(et->leftChild);
        et->rightChild = IFF(et->rightChild);
    }
    return et;
}

// // convert IFF expression tree to NNF expression tree
BT *NNF (BT *etI)
{
    if(etI->element == '!'){
        BT *replica;
        replica = etI->rightChild;
        if(replica->element == '!'){
            etI = NNF(replica->rightChild);
        }
        else if(replica->element == '|'){
            replica->element = '&';
            etI = replica;
            BT *x, *y;
            x = createNode('!');
            y = createNode('!');
            x->rightChild = replica->leftChild;
            y->rightChild = replica->rightChild;
            etI->leftChild = x;
            etI->rightChild = y;
            etI->leftChild = NNF(etI->leftChild);
            etI->rightChild = NNF(etI->rightChild);
        }
        else if(replica->element == '&'){
            replica->element = '|';
            etI = replica;
            BT *x, *y;
            x = createNode('!');
            y = createNode('!');
            x->rightChild = replica->leftChild;
            y->rightChild = replica->rightChild;
            etI->leftChild = x;
            etI->rightChild = y;
            etI->leftChild = NNF(etI->leftChild);
            etI->rightChild = NNF(etI->rightChild);
        }
    }
    else if(etI->element == '&' || etI->element == '|'){
        etI->leftChild = NNF(etI->leftChild);
        etI->rightChild = NNF(etI->rightChild);
    }
    return etI;
}

// // convert NNF expression tree to CNF expression tree
BT *CNF (BT *etN)
{
    if(etN->element == '&'){
        etN->leftChild = CNF(etN->leftChild);
        etN->rightChild = CNF(etN->rightChild);
    }
    else if(etN->element == '|'){
        BT *x, *y;
        x = etN->leftChild;
        y = etN->rightChild;
        if(x->element == '&'){
            etN->element = '&';
            x->element = '|';
            BT *temp;
            temp = createNode('|');
            etN->rightChild = temp;
            temp->leftChild = x->rightChild;
            temp->rightChild = y;
            x->rightChild = y;
            etN->leftChild = CNF(etN->leftChild);
            etN->rightChild = CNF(etN->rightChild);
        }
        else if(y->element == '&'){
            etN->element = '&';
            y->element = '|';
            BT *temp;
            temp = createNode('|');
            etN->leftChild = temp;
            temp->leftChild = x;
            temp->rightChild = y->leftChild;
            y->leftChild = x;
            etN->leftChild = CNF(etN->leftChild);
            etN->rightChild = CNF(etN->rightChild);
        }
    }
    return etN;
}

// // convert NNF expression tree to DNF expression tree
BT *DNF (BT *etN)
{
    if(etN->element == '|'){
        etN->leftChild = DNF(etN->leftChild);
        etN->rightChild = DNF(etN->rightChild);
    }
    else if(etN->element == '&'){
        BT *x, *y;
        x = etN->leftChild;
        y = etN->rightChild;
        if(x->element == '|'){
            etN->element = '|';
            x->element = '&';
            BT *temp;
            temp = createNode('&');
            etN->rightChild = temp;
            temp->leftChild = x->rightChild;
            temp->rightChild = y;
            x->rightChild = y;
            etN->leftChild = DNF(etN->leftChild);
            etN->rightChild = DNF(etN->rightChild);
        }
        else if(y->element == '|'){
            etN->element = '|';
            y->element = '&';
            BT *temp;
            temp = createNode('&');
            etN->leftChild = temp;
            temp->leftChild = x;
            temp->rightChild = y->leftChild;
            y->leftChild = x;
            etN->leftChild = DNF(etN->leftChild);
            etN->rightChild = DNF(etN->rightChild);
        }
    }
    return etN;
}

// // exhaustive search for checking validity / satisfiability
void CHECK (BT *et)
{
    int valid = 1, sat = 0;
    unsigned int noProp, i;
    PV *arr;
    printf("Enter Number of Propositions: ");
    scanf("%u",&noProp);
    char c;
    scanf("%c", &c);
    arr = (PV *)malloc(noProp * sizeof(PV));
    printf("Enter Proposition Names (<SPACE> Separated): ");
    for (i = 0; i < noProp; i++) {
        scanf(" %c", &arr[i].prop);
    }
    for (int x = 0; x < pow(2, noProp); ++x){
        int result;
        for (int i = 0; i < noProp; ++i){
            int y = 1 << (noProp-1-i);
            arr[i].val = (y & x) >> (noProp-1-i);
        }
        printf("\n");
        printf("{ ");
        for (int i = 0; i < noProp; ++i){
            printf("(%c = %d) ", arr[i].prop, arr[i].val);
        }
        printf("}  : ");
        result = EVAL(et, arr);
        printf("%d\n", result);
        if(result == 0) valid = 0;
        if(result == 1) sat = 1;
    }
    printResult(valid,sat);
}

// /**********************************************************/
// /******************* YOUR CODE ENDS HERE ******************/
// /**********************************************************/

// main routine
int main ()
{
    char formula[MAX], *pfForm;
    int len, i;
    
    BT *et, *etI, *etN, *etDup, *etC, *etD;
    int *varr;
    PV *pvarr;
    int result;
    
    // scan propositional formula from user input
    printf("\nEnter Propositional Logic Formula: ");
    scanf("%[^\n]", formula);
    
    // internal formula string with operators as, AND (&), OR (|), NOT (!), IMPLY (-) and IFF (~)
    len = strlen(formula);
    for(i = 0; i < len; i++){
        if(formula[i] == '<'){ // denoting iff operator (<->) using ~
            formula[i] = ' ';
            formula[i+1] = '~';
        }
        if(formula[i] == '>'){ // denoting imply operator (->) using -
            formula[i] = ' ';
        }
    }
    
    // postfix form generation from represented formula string
    pfForm = genPostFixFormula(formula);
    
    // display postfix form of the internally represented formula
    displayPfForm(pfForm);
    
    //internal postfix formula string with operators as, AND (&), OR (|), NOT (!), IMPLY (-) and IFF (~)
    printf("\n++++ PostFix Format of the Propositional Formula ++++\n('-' used for '->' and '~' used for '<->')\n");
    printf("YOUR INPUT STRING: %s\n", pfForm);
    
    
    
    /**********************************************************/
    /********** YOUR CODE ENABLES THE FOLLOWING PARTS *********/
    /**********************************************************/



    printf("\n++++ Expression Tree Generation ++++");
    et = ETF(pfForm, 0, strlen(pfForm)-1);
    printf("\nOriginal Formula (from Expression Tree):");
    ETP(et);
    printf("\n");
    
    printf("\n++++ Expression Tree Evaluation ++++\n");
    pvarr = scanPropValueInput();
    result = EVAL(et, pvarr);
    printf("\nThe Formula is Evaluated as: ");
    (result) ? printf("True\n") : printf("False\n");
    
    printf("\n++++ IFF Expression Tree Conversion ++++");
    etI = IFF(et);
    printf("\nFormula in Implication Free Form (IFF from Expression Tree):");
    ETP(etI);
    printf("\n");
    
    printf("\n++++ NNF Expression Tree Conversion ++++");
    etN = NNF(etI);
    printf("\nFormula in Negation Normal Form (NNF from Expression Tree):");
    ETP(etN);
    printf("\n");
    
    etDup = duplicate(etN); // keeping a duplicate copy for DNF conversion
    
    printf("\n++++ CNF Expression Tree Conversion ++++");
    etC = CNF(etN);
    printf("\nFormula in Conjunctive Normal Form (CNF from Expression Tree):");
    ETP(etC);
    printf("\n");
    
    printf("\n++++ DNF Expression Tree Conversion ++++");
    etD = DNF(etDup);
    printf("\nFormula in Disjunctive Normal Form (DNF from Expression Tree):");
    ETP(etD);
    printf("\n");
    
    printf("\n++++ Exhaustive Search from Expression Tree for Validity / Satisfiability Checking ++++");
    printf("\n");
    CHECK (et);
    printf("\n");
    
    // /**********************************************************/
    
    
    return 0;
}