# VSIDS branching heuristic

The **variable state independent decaying sum (VSIDS)** heuristic keeps a nonnegative **activity** for every variable and a current **increment** $\iota > 0$. After each conflict, the activity of every variable occurring in the recorded (learned) clause is increased by $\iota$, and then $\iota$ is multiplied by a factor $1/d$ with a fixed decay $0 < d < 1$; this is equivalent to multiplying all activities by $d$ after each conflict, and activities and $\iota$ are scaled down together when they grow too large. A decision picks an unassigned variable of maximum activity. This is the variable-based form of MiniSat; Chaff's original scores literals, bumps the literals of each added clause, and periodically divides all scores by a constant. Later solvers also bump the variables of the reason clauses resolved during conflict analysis.

## Depends on

- [Abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/abstract-dpll-with-learning.md)

## Sources

- M. W. Moskewicz, C. F. Madigan, Y. Zhao, L. Zhang and S. Malik, "Chaff: Engineering an Efficient SAT Solver", Proceedings of the 38th Design Automation Conference, 2001.
- N. Eén and N. Sörensson, "An Extensible SAT-solver", Theory and Applications of Satisfiability Testing (SAT 2003), LNCS 2919, Springer, 2004, Section 4.6 (activity heuristics).
