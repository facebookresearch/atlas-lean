# Soundness of CDCL at a decision-free conflict

Let $F$ be a CNF formula. If a state reachable from the initial state of CDCL on $F$ is in conflict and its trail has no decided literal, then $F$ is unsatisfiable. It is therefore sound to report unsatisfiability in this state. The theorem is not a termination or reporting guarantee: the transition system can keep learning derivable clauses without clearing the conflict.
