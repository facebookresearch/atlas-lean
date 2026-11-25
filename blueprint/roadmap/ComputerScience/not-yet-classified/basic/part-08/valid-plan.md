# Valid plan

A plan, a list of operators, is valid for a STRIPS task when every operator in it belongs to the task and executing it from the initial state reaches a goal state: a state containing every positive goal atom and none of the negative goal atoms. Each step applies its operator when the operator's preconditions hold and leaves the state unchanged otherwise (Bylander's total result semantics).
