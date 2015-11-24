//Email: sixueliu@gmail.com
//Personal Website: http://iiis.tsinghua.edu.cn/2013211593/

#include <sys/times.h> //these two h files are for linux
#include <unistd.h>
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cmath>
#include <limits.h>
#include <float.h>
#include <getopt.h>
#include <signal.h>

using namespace std;

int	noise;
int	rd_noise;
int	seed;
//cutoff
int	maxtime, maxflips;


//These are necessary data structures
#define MAX_VARS    4000010
#define MAX_CLAUSES 17000000

/*parameters of the instance*/
//Note that variabless' and clauses' indices begin with 1, not 0
int     num_vars;			//var index from 1 to num_vars
int     num_clauses;		//clause index from 1 to num_clauses


// Define a data structure for a literal in clauses
int	*var_poslit[MAX_VARS];				//var_lit[v][j]: the clause number of the clause that the j'th positive literal of v occurs in.
// the last clause id is 0, as an indicator of ending
int	*var_neglit[MAX_VARS];

int	var_poslit_count[MAX_VARS];
int	var_neglit_count[MAX_VARS];

//unsat clauses stack
int	unsat_stack[MAX_CLAUSES];		//store the unsat clauses
int	unsat_stack_fill_pointer;		//the number of unsat clauses
int	index_in_unsat_stack[MAX_CLAUSES];//which position is a clause in the unsat_stack

struct lit {
     	int var_num;		//variable num, begin with 1
     	bool sense;			//is 1 for positive literals, 0 for negative literals.
};
lit	*clause_lit[MAX_CLAUSES];			//clause_lit[i][j] means the j'th literal of clause i.
int	clause_lit_count[MAX_CLAUSES]; 		// amount of literals in each clause				

bool     cur_soln[MAX_VARS];	//the current solution, with 1's for True variables, and 0's for False variables

int     sat_count[MAX_CLAUSES];	// the number of satisfied literals in a clause, 0 means unsat		

// random order
int	order_3sat[6][3] = {0,1,2, 0,2,1, 1,0,2, 1,2,0, 2,0,1, 2,1,0};

void flip0(int flipvar)
{
	int c;
	int * truep, * falsep;
	cur_soln[flipvar] = 1 - cur_soln[flipvar];
	if (cur_soln[flipvar]==1) {truep=var_poslit[flipvar]; falsep=var_neglit[flipvar];}
	else {truep = var_neglit[flipvar]; falsep = var_poslit[flipvar];}
	for (; (c=*truep)!=0; ++truep) {
		++sat_count[c];
		if (sat_count[c] == 1) { // sat_count from 0 to 1
			unsat_stack[index_in_unsat_stack[c]] = unsat_stack[--unsat_stack_fill_pointer];
			index_in_unsat_stack[unsat_stack[index_in_unsat_stack[c]]] = index_in_unsat_stack[c];
		}
	}
	for (; (*falsep)!=0; ++falsep) //break=0,no clause will be unsat
		--sat_count[*falsep];
}
void flip2(int flipvar)
{
	int c;
	int * truep, * falsep;
	cur_soln[flipvar] = 1 - cur_soln[flipvar];
	if (cur_soln[flipvar]==1) {truep=var_poslit[flipvar]; falsep=var_neglit[flipvar];}
	else {truep = var_neglit[flipvar]; falsep = var_poslit[flipvar];}
	for (; (c=*truep)!=0; truep++) {
		++sat_count[c];
		if (sat_count[c] == 1) { // sat_count from 0 to 1
			unsat_stack[index_in_unsat_stack[c]] = unsat_stack[--unsat_stack_fill_pointer];
			index_in_unsat_stack[unsat_stack[index_in_unsat_stack[c]]] = index_in_unsat_stack[c];
		}
	}
	for (; (c=*falsep)!=0; ++falsep) {
		--sat_count[c];
		if (sat_count[c] == 0) { //	last_unsatvar[c]=flipvar;
			unsat_stack[unsat_stack_fill_pointer] = c;
			index_in_unsat_stack[c] = unsat_stack_fill_pointer++;
		}
	}
}




void separating_non_caching_3sat() // choose variable according to SKC
{
	int		c = unsat_stack[rand()%unsat_stack_fill_pointer];
	int		v0,v1,v2;
	int		oi = rand() % 6; // generate a random order
	// These are clause pointers for each variable's occurences
	int		*truep0, *truep1, *truep2; // using pointer iterator is faster

	//find 0-break var as early as possible
	// var 0
	v0 = clause_lit[c][order_3sat[oi][0]].var_num;
	truep0 = (cur_soln[v0])? var_poslit[v0]:var_neglit[v0];
	for(; sat_count[*truep0]!=1; ++truep0);
	if (*truep0 == 0) {
		flip0(v0);
		return;
	}
	// var 1
	v1 = clause_lit[c][order_3sat[oi][1]].var_num;
	truep1 = (cur_soln[v1])? var_poslit[v1]:var_neglit[v1];
	for(; sat_count[*truep1]!=1; ++truep1);
	if (*truep1 == 0) {
		flip0(v1);
		return;
	}
	// var 2
	v2 = clause_lit[c][order_3sat[oi][2]].var_num;
	truep2 = (cur_soln[v2])? var_poslit[v2]:var_neglit[v2];
	for(; sat_count[*truep2]!=1; ++truep2);
	if (*truep2 == 0) {
		flip0(v2);
		return;
	}

	//random
	if (rand() < rd_noise) {
		flip2(clause_lit[c][rand() % 3].var_num);
		return;
	}
	//greedy

	// I tried to expand the same process with findind 0-break to find i-break, but the gain seems minor

	// the break values are at least 1
	// return the first encounted var with minimal break value
	int		c0, c1, c2;
	int		bestvar;
	int		best_bbreak = 0;
	int		bbreakv = 0;
	// the iteration starts at the stop position when finding 0-break var 


	// var 0
	for(c0 = *(truep0++); (*truep0)!=0; ++truep0) {
		if (sat_count[*truep0]==1) ++best_bbreak;
	}
	if (best_bbreak == 0) { // which implies break == 1, is the minimal break
		flip0(v0);
		//only c0 will be unsat
		unsat_stack[unsat_stack_fill_pointer] = c0;
		index_in_unsat_stack[c0] = unsat_stack_fill_pointer++;
		return;
	}
	bestvar = v0;
	// var 1
	for(c1 = *(truep1++); (*truep1)!=0; ++truep1) {
		if (sat_count[*truep1]==1) {
			if (bbreakv == best_bbreak - 1) break;
			++bbreakv;					
		}
	}
	if(*truep1 == 0) {// implies bbreakv < best_bbreak
		if (bbreakv == 0) {
			flip0(v1);
			//only c1 will be unsat
			unsat_stack[unsat_stack_fill_pointer] = c1;
			index_in_unsat_stack[c1] = unsat_stack_fill_pointer++;
			return;
		}
		best_bbreak = bbreakv;
		bestvar = v1;
	}
	// var 2
	bbreakv = 0;
	for(c2 = *(truep2++); (*truep2)!=0; ++truep2) {
		if (sat_count[*truep2]==1) {
			if (bbreakv == best_bbreak - 1) break;
			++bbreakv;					
		}
	}
	if(*truep2 == 0) {// implies bbreakv < best_bbreak
		if (bbreakv == 0) {
			flip0(v2);
			//only c2 will be unsat
			unsat_stack[unsat_stack_fill_pointer] = c2;
			index_in_unsat_stack[c2] = unsat_stack_fill_pointer++;
			return;
		}
		else {
			flip2(v2);
			return;
		}
	}
	flip2(bestvar);
}

int build_instance(char *filename)
{
	int	max_clause_len = 0, min_clause_len = 2013211593;
	char    line[1024];
	char    tempstr1[10];
	char    tempstr2[10];
	int     cur_lit;
	int     i,j;
	int		v,c;//var, clause
	
	ifstream infile(filename);
	if(infile==NULL) {
		cout<<"Invalid filename: "<< filename<<endl;
		return 0;
	}

	/*** build problem data structures of the instance ***/
	infile.getline(line,1024);
	while (line[0] != 'p') infile.getline(line,1024);

	sscanf(line, "%s %s %d %d", tempstr1, tempstr2, &num_vars, &num_clauses);
	
	for (c = 1; c <= num_clauses; c++) clause_lit_count[c] = 0;
	for (v=1; v<=num_vars; ++v) {
		var_poslit_count[v] = 0;
		var_neglit_count[v] = 0;
	}
	
	int *temp_lit = new int [num_vars+1];//local
		
	//Now, read the clauses, one at a time.
	for (c = 1; c <= num_clauses; ++c) {
		infile>>cur_lit;
		while (cur_lit != 0) { 
			temp_lit[clause_lit_count[c]] = cur_lit;
			clause_lit_count[c]++;
			infile>>cur_lit;
		}
		
		clause_lit[c] = new lit[clause_lit_count[c]+1];
		
		max_clause_len = max(max_clause_len, clause_lit_count[c]);
		min_clause_len = min(min_clause_len, clause_lit_count[c]);
		for(i=0; i<clause_lit_count[c]; ++i) {
			//clause_lit[c][i].clause_num = c;
			clause_lit[c][i].var_num = abs(temp_lit[i]);
			if (temp_lit[i] > 0) {
				clause_lit[c][i].sense = 1;
				var_poslit_count[clause_lit[c][i].var_num]++;
			}
			else {
				clause_lit[c][i].sense = 0;
				var_neglit_count[clause_lit[c][i].var_num]++;
			}
		}
		
		clause_lit[c][i].var_num = 0; 
	}
	infile.close();
	
	delete[] temp_lit;
	
	//creat var literal arrays
	for (v=1; v<=num_vars; ++v) {
		var_poslit[v] = new int[var_poslit_count[v]+1];
		var_poslit_count[v] = 0;	//reset to 0, for build up the array
		var_neglit[v] = new int[var_neglit_count[v]+1];
		var_neglit_count[v] = 0;
	}
	//scan all clauses to build up var literal arrays
	for (c = 1; c <= num_clauses; ++c) {
		for(i=0; i<clause_lit_count[c]; ++i) {
			v = clause_lit[c][i].var_num;
			
			if(clause_lit[c][i].sense==1) {
				var_poslit[v][var_poslit_count[v]] = c;
				++var_poslit_count[v];
			}
			else {
				var_neglit[v][var_neglit_count[v]] = c;
				++var_neglit_count[v];
			}
		}
	}
	//set sentinel
	sat_count[0] = 1;
	for (v=1; v<=num_vars; ++v) {
		var_poslit[v][var_poslit_count[v]] = 0;
		var_neglit[v][var_neglit_count[v]] = 0;
	}
	//cout << max_clause_len << '\t' << min_clause_len << endl;
	if (max_clause_len != 3 || max_clause_len != min_clause_len) {
		cout << endl << "Sorry, this is just a sample program for Exact-3-SAT." << endl;
		cout << "Please contact sixueliu@gmail.com to get the full version." << endl << endl;
		return 2;
	}
	return 1;
}

void free_memory()
{
	int i, j;
	for (i = 1; i <= num_clauses; i++) {
		delete[] clause_lit[i];
	}
	
	for(i=1; i<=num_vars; ++i) {
		delete[] var_poslit[i];
		delete[] var_neglit[i];
	}
}
//initiation of the algorithm
void init()
{
	int 		v,c;
	int			i,j;
	int			clause;
	
	//init solution
	for (v = 1; v <= num_vars; v++)
		cur_soln[v] = rand() & 1;
		//cur_soln[v] = 1;

	/* figure out sat_count, and init unsat_stack */
	unsat_stack_fill_pointer = 0;
	for (c=1; c<=num_clauses; ++c) {
		sat_count[c] = 0;
		
		for(j=0; j<clause_lit_count[c]; ++j) {
			if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense) {
				++sat_count[c];
			}
		}

		if (sat_count[c] == 0) {
			unsat_stack[unsat_stack_fill_pointer] = c;
			index_in_unsat_stack[c] = unsat_stack_fill_pointer++;
		}
	}
}





/*the following functions are non-algorithmic*/

void print_solution()
{
     int    i;

    cout<<"v ";
    for (i=1; i<=num_vars; i++) {
		if(cur_soln[i]==0) cout<<"-";
		cout<<i;
		
		if(i%10==0) 
		{
			cout<<endl;
			cout<<"v ";
		}
		else cout<<' ';
     }
     cout<<"end"<<endl;
}


int verify_sol()
{
	int c,j; 
	int flag;
	
	for (c = 1; c<=num_clauses; ++c) {
		flag = 0;
		for(j=0; j<clause_lit_count[c]; ++j)
			if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense) {flag = 1; break;}

		if(flag ==0){ //output the clause unsatisfied by the solution
			cout<<"clause "<<c<<" is not satisfied"<<endl;
			
			for(j=0; j<clause_lit_count[c]; ++j) {
				if(clause_lit[c][j].sense==0)cout<<"-";
				cout<<clause_lit[c][j].var_num<<" ";
			}
			cout<<endl;
			
			for(j=0; j<clause_lit_count[c]; ++j)
				cout<<cur_soln[clause_lit[c][j].var_num]<<" ";
			cout<<endl;

			return 0;
		}
	}
	return 1;
}

void parse_and_set_parameters(int argc, char *argv[]) {
	//define the argument parser
	static struct option long_options[] = {
			{"maxflips", required_argument, 0, 'f' },
			{"maxtime", required_argument, 0, 't' },
			{"noise", required_argument, 0, 'n' },
			{"seed", required_argument, 0, 's' },
	};

	while (optind < argc) {
		int index = -1;
		struct option * opt = 0;
		int result = getopt_long(argc, argv, "f:t:n:s:", long_options, &index); //
		if (result == -1)
			break; /* end of list */
		switch (result) {
		case 'f':
			maxflips = atoi(optarg);
			break;
		case 't':
			maxtime = atoi(optarg);
			break;
		case 'n':
			noise = atoi(optarg);
			break;
		case 's':
			seed = atoi(optarg);
			break;
		default:
			break;
		}
	}
	if (optind == argc) {
		printf("ERROR: Parameter String not correct!\n");
		cout << "Please use the following format:\n";
		cout << "./wsat -s seed -n noise*1000 -t maxtime -f maxflips filename" << endl;
		exit(0);
	}
	if (build_instance(argv[optind]) != 1)
		exit(-1);

	srand(seed);
	rd_noise = (double)noise / 1000 * RAND_MAX;
}

int main(int argc, char* argv[])
{
	double	comp_time;
	struct	tms	start, stop;	
	int	cutoff_time;
	
	times(&start);


	//init par
	seed = times(0);
	maxtime = 10;
	maxflips = 1000000;
	noise = 567;

	parse_and_set_parameters(argc, argv);
	
	cout << endl << "Noise = " << (double)noise/1000 << endl;
	cout << "Seed = " << seed << endl;
	cout << "Maxtime = " << maxtime << endl;
	cout << "Maxflips = " << maxflips << endl;

	int	i, j;
	int	lowest_unsat_num = num_clauses;
	for (i = 0; i < maxtime; ++i) {
		init();
		for (j = 0; j < maxflips; ++j) {
			lowest_unsat_num = min(lowest_unsat_num, unsat_stack_fill_pointer);
			if (unsat_stack_fill_pointer == 0) { //solution found!
    				times(&stop);
				comp_time = double(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
				//print_solution();
				printf("\nRunning Time : %.2lf", comp_time);
				printf("\nSteps : %lld\n\n", (long long)(maxflips) * i + j);
				free_memory();
				return 0;
			}
			separating_non_caching_3sat();
		}
	}
	cout << endl << "The lowest number of unsat clauses number found: " << lowest_unsat_num << endl << endl;
	return 0;
}
