#include"BTSolver.hpp"

using namespace std;

// =====================================================================
// Constructors
// =====================================================================

BTSolver::BTSolver ( SudokuBoard input, Trail* _trail,  string val_sh, string var_sh, string cc )
: sudokuGrid( input.get_p(), input.get_q(), input.get_board() ), network( input )
{
	valHeuristics = val_sh;
	varHeuristics = var_sh; 
	cChecks =  cc;

	trail = _trail;
}

// =====================================================================
// Consistency Checks
// =====================================================================

// Basic consistency check, no propagation done
bool BTSolver::assignmentsCheck ( void )
{
	for ( Constraint c : network.getConstraints() )
		if ( ! c.isConsistent() )
			return false;

	return true;
}

// =================================================================
// Arc Consistency
// =================================================================
bool BTSolver::arcConsistency ( void )
{
	vector<Variable*> toAssign;
	vector<Constraint*> RMC = network.getModifiedConstraints();
	for (int i = 0; i < RMC.size(); ++i)
	{
		vector<Variable*> LV = RMC[i]->vars;
		for (int j = 0; j < LV.size(); ++j)
		{
			if(LV[j]->isAssigned())
			{
				vector<Variable*> Neighbors = network.getNeighborsOfVariable(LV[j]);
				int assignedValue = LV[j]->getAssignment();
				for (int k = 0; k < Neighbors.size(); ++k)
				{
					Domain D = Neighbors[k]->getDomain();
					if(D.contains(assignedValue))
					{
						if (D.size() == 1)
							return false;
						if (D.size() == 2)
							toAssign.push_back(Neighbors[k]);
						trail->push(Neighbors[k]);
						Neighbors[k]->removeValueFromDomain(assignedValue);
					}
				}
			}
		}
	}
	if (!toAssign.empty())
	{
		for (int i = 0; i < toAssign.size(); ++i)
		{
			Domain D = toAssign[i]->getDomain();
			vector<int> assign = D.getValues();
			trail->push(toAssign[i]);
			toAssign[i]->assignValue(assign[0]);
		}
		return arcConsistency();
	}
	return network.isConsistent();
}

/**
 * Part 1 TODO: Implement the Forward Checking Heuristic
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *	 the square's neighbors.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
 * 		   The bool is true if assignment is consistent, false otherwise.
 */
pair<map<Variable*,Domain>,bool> BTSolver::forwardChecking ( void )
{
	pair<map<Variable*, Domain>, bool> retPair;

	for(Variable* v : network.getVariables()) // get variables
	{
		if(v->isAssigned()) // check if assigned
		{
			int check = v->getAssignment(); // get assignment
			ConstraintNetwork::VariableSet neighbors = network.getNeighborsOfVariable(v); // get neighbors

			for(Variable* neighbor : neighbors) // loop through neighbors
			{
				int j = 0;
				while(neighbor->getDomain().size() > 0 && !(neighbor->isAssigned()))
				{
					if(neighbor->getDomain().getValues()[j] == check) // check if neighbor domain value == assignment
					{
						trail->push(neighbor); // trail.push neighbor variables before changing their domain
						neighbor->removeValueFromDomain(check); // remove value from domain
						retPair.first[neighbor] = neighbor->getDomain();
						break; // get next neighbor
					}
					++j;
					if(j == neighbor->getDomain().size())
						break;
				}
			}
		}
	}

	retPair.second = network.isConsistent();

	return retPair;
}

/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *	 the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *	 then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during 
 *		 the whole NorvigCheck propagation, and mapped to the values that they were assigned. 
 *		 The bool is true if assignment is consistent, false otherwise.
 */

/*
pair<map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
	pair<map<Variable*,int>,bool> retPair;
	
	// step (1) copied from Part 1 forwardChecking() function.
	for(Variable* v : network.getVariables()) // get variables
	{
		if(v->isAssigned()) // check if assigned
		{
			int check = v->getAssignment(); // get assignment
			ConstraintNetwork::VariableSet neighbors = network.getNeighborsOfVariable(v); // get neighbors

			for(Variable* neighbor : neighbors) // loop through neighbors
			{
				//int j = 0;
				//while(neighbor->getDomain().size() > 0 && !(neighbor->isAssigned()))
				//{
					if(neighbor->getDomain().contains(check)) // check if neighbor domain value == assignment
					{
						trail->push(neighbor); // trail.push neighbor variables before changing their domain
						neighbor->removeValueFromDomain(check); // remove value from domain
						//break; // get next neighbor
					}
					//++j;
					//if(j == neighbor->getDomain().size())
						//break;
				//}
			}
		}
	}


	for(Constraint c : network.getConstraints()) // get constraints
	{
		vector<int> domainVec = {0,0,0,0,0,0,0,0,0}; // keep track of [1,9] domain values

		// marks seen
		for(Variable* v: c.vars)
		{
			Domain::ValueSet domain = v->getDomain().getValues();
			
			for(int i = 0; i < domain.size(); ++i)
				++domainVec[domain[i] - 1];	// increm domainVec index (val=1 is index 0, val=9 is index 8, etc.)
		}

		// print
		//for(int k = 0; k < domainVec.size(); ++k)
			//cout << domainVec[k] << ", ";
		//cout << "\n";

		// find var and sets value
		for(int i = 0; i < domainVec.size(); ++i)
		{
			if(domainVec[i] == 1)
			{
				int val = i + 1; // val to assign is vec index+1

				for(Variable* var : c.vars)
				{
					Domain::ValueSet domainVar = var->getDomain().getValues();

					for(int j = 0; j < domainVar.size(); ++j)
					{
						if(domainVar[j] == val)
						{
							cout << "up\n";
							trail->push(var); // trail.push variable before changing their domain
							var->removeValueFromDomain(val);
							var->assignValue(val);
							retPair.first[var] = val;
							//cout << "made it here\n";

						}
					}
				}
			}
		}
	}
	//cout << "here\n";

	retPair.second = network.isConsistent();
	return retPair;
}
*/
/*
pair<map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
	pair<map<Variable*,int>,bool> retPair;
	
	// step (1) copied from Part 1 forwardChecking() function.
	for(Variable* v : network.getVariables()) // get variables
	{
		if(v->isAssigned()) // check if assigned
		{
			int check = v->getAssignment(); // get assignment
			ConstraintNetwork::VariableSet neighbors = network.getNeighborsOfVariable(v); // get neighbors

			for(Variable* neighbor : neighbors) // loop through neighbors
			{
			    if(neighbor->getDomain().contains(check)) // check if neighbor domain value == assignment
                {
                    trail->push(neighbor); // trail.push neighbor variables before changing their domain
                    neighbor->removeValueFromDomain(check); // remove value from domain
                }
                v->setModified(false);
			}
		}
	}


	for(Constraint c : network.getConstraints()) // get constraints
	{
		vector<int> domainVec = {0,0,0,0,0,0,0,0,0}; // keep track of [1,9] domain values

		// marks seen
		for(Variable* v: c.vars)
		{
			Domain::ValueSet domain = v->getDomain().getValues();
			
			for(int i = 0; i < domain.size(); ++i)
				++domainVec[domain[i] - 1];	// increm domainVec index (val=1 is index 0, val=9 is index 8, etc.)
		}

		// print
		//for(int k = 0; k < domainVec.size(); ++k)
		//	cout << domainVec[k] << ", ";
		//cout << "\n";

		// find var and sets value
		for(int i = 0; i < domainVec.size(); ++i)
		{
			if(domainVec[i] == 1)
			{
				int val = i + 1; // val to assign is vec index+1

				for(Variable* var : c.vars)
				{
					if(var->getDomain().contains(val))
					{
						trail->push(var); // trail.push variable before changing their domain
						var->removeValueFromDomain(val);
						var->assignValue(val);
						//retPair.first.insert({var, val});
						//ptr = mp.insert( pair<char, int>('a', 20) ); 
						//retPair.first.insert(pair<Variable*, int>(var, val));
						retPair.first.insert(pair<Variable*, int>(var, val));
					}
				}
			}
		}
	}

	retPair.second = network.isConsistent();
	return retPair;
}
*/
pair<map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
	pair<map<Variable*, int>, bool> retPair;

	// step (1) copied from Part 1 forwardChecking() function.
	/*
	for(Variable* v : network.getVariables()) // get variables
	{
		if(v->isAssigned()) // check if assigned
		{
			int check = v->getAssignment(); // get assignment
			ConstraintNetwork::VariableSet neighbors = network.getNeighborsOfVariable(v); // get neighbors

			for(Variable* neighbor : neighbors) // loop through neighbors
			{
			    if(neighbor->getDomain().contains(check)) // check if neighbor domain value == assignment
                {
                    trail->push(neighbor); // trail.push neighbor variables before changing their domain
                    neighbor->removeValueFromDomain(check); // remove value from domain
                }
                v->setModified(false);
			}
		}
	}
	*/

	for(Variable* v : network.getVariables()) // get variables
	{
		if(v->isAssigned()) // check if assigned
		{
			int check = v->getAssignment(); // get assignment
			ConstraintNetwork::VariableSet neighbors = network.getNeighborsOfVariable(v); // get neighbors

			for(Variable* neighbor : neighbors) // loop through neighbors
			{
				int j = 0;
				while(neighbor->getDomain().size() > 0 && !(neighbor->isAssigned()))
				{
					if(neighbor->getDomain().getValues()[j] == check) // check if neighbor domain value == assignment
					{
						trail->push(neighbor); // trail.push neighbor variables before changing their domain
						neighbor->removeValueFromDomain(check); // remove value from domain
						break; // get next neighbor
					}
					++j;
					if(j == neighbor->getDomain().size())
						break;
				}
			}
		}
	}

	//map<Variable*, int> myMap;

	for(Constraint c : network.getConstraints()) // get variables
	{
		vector<int> domainVec = {0,0,0,0,0,0,0,0,0};

		for(Variable* v : c.vars) // c.vars
		{
			Domain::ValueSet domain = v->getDomain().getValues();
			
			for(int i = 0; i < domain.size(); ++i)
				++domainVec[domain[i] - 1];
		}

		for(int i = 0; i < domainVec.size(); ++i)
		{
			if(domainVec[i] == 1)
			{
				int val = i + 1;
				for(Variable* var : c.vars)
				{
					if(!var->isAssigned())
					{
						if(var->getDomain().contains(val))
						{
							trail->push(var);
							var->assignValue(val);
							//myMap.insert(pair<Variable*,int>(var, val));
							retPair.first.insert(pair<Variable*,int>(var, val));
						}
					}
				}
			}
		}
	}

	//retPair.first = myMap;
	retPair.second = network.isConsistent();

	return retPair;
}

/**
 * Optional TODO: Implement your own advanced Constraint Propagation
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
bool BTSolver::getTournCC ( void )
{
	return false;
}

// =====================================================================
// Variable Selectors
// =====================================================================

// Basic variable selector, returns first unassigned variable
Variable* BTSolver::getfirstUnassignedVariable ( void )
{
	for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) )
			return v;

	// Everything is assigned
	return nullptr;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */
Variable* BTSolver::getMRV ( void )
{
	Variable* minVariable = nullptr;
	for (Variable* var : network.getVariables()) {
		// confirm var is unassigned
		if (!(var->isAssigned())) {
			// update minVar if it's null or if we find a new var with smaller domain
			if (minVariable == nullptr or var->getDomain().size() < minVariable->getDomain().size())
				minVariable = var;
		}
	}
	return minVariable;
}

/**
 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
 *				with Degree Heuristic as a Tie Breaker
 *
 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
 * 		   If there are multiple variables that have the same smallest domain with the same number 
 * 		   of unassigned neighbors, add them to the vector of Variables.
 *		 If there is only one variable, return the vector of size 1 containing that variable.
 */
vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
	vector<Variable*> retVec;
	
	// find minDomainSize
	int minDomainSize = 9;
	for(Variable* v : network.getVariables())
	{
		if(!v->isAssigned())
		{
			int domainSize = v->getDomain().size();
			if(domainSize < minDomainSize)
				minDomainSize = domainSize;
		}
	}

	// find all Variable* of size minDomainSize
	// push all to vector<Variable*> minVars
	vector<Variable*> minVars;
	for(Variable* v : network.getVariables())
	{
		if(!v->isAssigned())
		{
			if(v->getDomain().size() == minDomainSize)
				minVars.push_back(v);
		}
	}

	if(minVars.size() > 1)
	{
		// scroll through vector<Variable*> minVars
		// find numAffectedNeighbors for each Variable*
		// push (Variable*, numAffectedNeighbors) to map<Variable*, int>
		map<Variable*, int> maxAffecting;
		for(int i = 0; i < minVars.size(); ++i)
		{
			Domain::ValueSet domain = minVars[i]->getDomain().getValues();
			int numAffectedNeighbors = 0;
				
			for(int j = 0; j < domain.size(); ++j)
			{
				char val = domain[j];
				for(Variable* neighbor : network.getNeighborsOfVariable(minVars[i]))
				{
					if(neighbor->getDomain().contains(val))
					{
						++numAffectedNeighbors;
					}
				}
			}
			maxAffecting.insert(pair<Variable*, int>(minVars[i], numAffectedNeighbors));
		}

		// iterate through map, find maxAffect for mapValue->second
		// iterate through map and assigValue() to Variables* with affect=max
		int maxAffect = 0;
		for(map<Variable*, int>::iterator iter = maxAffecting.begin(); iter != maxAffecting.end(); ++iter)
		{
			if(iter->second > maxAffect)
				maxAffect = iter->second;
		}
		for(map<Variable*, int>::iterator iter = maxAffecting.begin(); iter != maxAffecting.end(); ++iter)
		{
			if(iter->second == maxAffect)
				retVec.push_back(iter->first);
		}
	}
	else
		retVec.push_back(minVars[0]);

	return retVec;
}

/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
Variable* BTSolver::getTournVar ( void )
{
	return nullptr;
}

// =====================================================================
// Value Selectors
// =====================================================================

// Default Value Ordering
vector<int> BTSolver::getValuesInOrder ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
	sort( values.begin(), values.end() );
	return values;
}

/**
 * Part 1 TODO: Implement the Least Constraining Value Heuristic
 *
 * The Least constraining value is the one that will knock the least
 * values out of it's neighbors domain.
 *
 * Tie Breaker: If the list of values to be returned is [2, 1, 7, 5, 3]
 * 		 with 7 and 5 affecting the same amount of variables. Then the
 *		 correct list to be returned is [2, 1, 5, 7, 3].
 *
 * Return: A list of v's domain sorted by the LCV heuristic
 *		 The LCV is first and the MCV is last
 */
vector<int> BTSolver::getValuesLCVOrder ( Variable* v )
{
	// size(), getDomain(), getValues()
	vector<int> values = v->getDomain().getValues();
	ConstraintNetwork::VariableSet neighbors = network.getNeighborsOfVariable(v);

	map<int,int> process_map;

	int curCount = 0;
	for(int i = 0; i < v->getDomain().getValues().size(); ++i)
	{ 
		int check = values[i]; // grab a value from domain of given square
		
		for(Variable* neighbor : neighbors) // grabs neighbor domain and checks constraints
		{
			for(int j = 0; j < neighbor->getDomain().getValues().size(); ++j)
			{
				int neiCheck = neighbor->getDomain().getValues()[j];
				if(check == neiCheck)
				{
					++curCount;
				}
			}
			process_map[check] = process_map[check] + curCount;
			curCount = 0;
		}
	}

	// separate keys and values of process_map
	vector<int> vals;
	vector<int> keys;
	for(map<int,int>::iterator it = process_map.begin(); it != process_map.end(); ++it)
	{
		keys.push_back(it->first);
		vals.push_back(it->second);
	}

	// sort values
	sort(vals.begin(), vals.end());

	// get keys of values into a vector
	vector<int> retKeys;
	vector<int> temp;
	for(int i = 0; i < vals.size(); ++i)
	{
		int find = vals[i]; // get value to search for its key
		for(map<int,int>::iterator it = process_map.begin(); it != process_map.end(); ++it)
		{
			if(find == it->second) // found value
			{
				temp.push_back(it->first);
				//remove it->first, it->second
				it->second = -1;
			}
		}
		// check for ties
		while(temp.size() > 0)
		{
			// find min in temp
			//int* min = min_element(temp.begin(), temp.end());
			vector<int>::iterator min = min_element(temp.begin(), temp.end());
			retKeys.push_back(*min);
			temp.erase(min);
		}
	}

	return retKeys;
}

/**
 * Optional TODO: Implement your own advanced Value Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
vector<int> BTSolver::getTournVal ( Variable* v )
{
	return vector<int>();
}

// =====================================================================
// Engine Functions
// =====================================================================

int BTSolver::solve ( float time_left)
{
	if (time_left <= 60.0)
		return -1;
	double elapsed_time = 0.0;
	clock_t begin_clock = clock();

	if ( hasSolution )
		return 0;

	// Variable Selection
	Variable* v = selectNextVariable();

	if ( v == nullptr )
	{
		for ( Variable* var : network.getVariables() )
		{
			// If all variables haven't been assigned
			if ( ! ( var->isAssigned() ) )
			{
				return 0;
			}
		}

		// Success
		hasSolution = true;
		return 0;
	}

	// Attempt to assign a value
	for ( int i : getNextValues( v ) )
	{
		// Store place in trail and push variable's state on trail
		trail->placeTrailMarker();
		trail->push( v );

		// Assign the value
		v->assignValue( i );

		// Propagate constraints, check consistency, recurse
		if ( checkConsistency() ) {
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock)/ CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if(check_status == -1) {
				return -1;
			}
			
		}

		// If this assignment succeeded, return
		if ( hasSolution )
			return 0;

		// Otherwise backtrack
		trail->undo();
	}
	return 0;
}

bool BTSolver::checkConsistency ( void )
{
	if ( cChecks == "forwardChecking" )
		return forwardChecking().second;

	if ( cChecks == "norvigCheck" )
		return norvigCheck().second;

	if ( cChecks == "tournCC" )
		return getTournCC();

	return assignmentsCheck();
}

Variable* BTSolver::selectNextVariable ( void )
{
	if ( varHeuristics == "MinimumRemainingValue" )
		return getMRV();

	if ( varHeuristics == "MRVwithTieBreaker" )
		return MRVwithTieBreaker()[0];

	if ( varHeuristics == "tournVar" )
		return getTournVar();

	return getfirstUnassignedVariable();
}

vector<int> BTSolver::getNextValues ( Variable* v )
{
	if ( valHeuristics == "LeastConstrainingValue" )
		return getValuesLCVOrder( v );

	if ( valHeuristics == "tournVal" )
		return getTournVal( v );

	return getValuesInOrder( v );
}

bool BTSolver::haveSolution ( void )
{
	return hasSolution;
}

SudokuBoard BTSolver::getSolution ( void )
{
	return network.toSudokuBoard ( sudokuGrid.get_p(), sudokuGrid.get_q() );
}

ConstraintNetwork BTSolver::getNetwork ( void )
{
	return network;
}
