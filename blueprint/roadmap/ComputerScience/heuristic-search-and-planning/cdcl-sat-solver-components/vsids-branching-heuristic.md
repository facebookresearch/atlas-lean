# VSIDS branching heuristic

The **variable state independent decaying sum (VSIDS)** heuristic keeps a nonnegative **activity** for every variable and a current **increment** $\iota > 0$. After each conflict, the activity of every variable occurring in the clauses resolved during conflict analysis (the learned clause and the reasons resolved on) is increased by $\iota$, and then $\iota$ is multiplied by a factor $1/d$ with $0 < d < 1$ (for example $d = 0.95$); activities and $\iota$ are rescaled together when they grow too large. A decision picks an unassigned variable of maximum activity, maintained in a binary max-heap keyed by activity.

## Depends on

- [Abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/abstract-dpll-with-learning.md)
- [Binary heap extraction removes one copy of the minimum](../../data-structures/heaps/binary-heap/extract-min-count.md)

## Sources

- M. W. Moskewicz, C. F. Madigan, Y. Zhao, L. Zhang and S. Malik, "Chaff: Engineering an Efficient SAT Solver", Proceedings of the 38th Design Automation Conference, 2001.
- N. Eén and N. Sörensson, "An Extensible SAT-solver", Theory and Applications of Satisfiability Testing (SAT 2003), LNCS 2919, Springer, 2004.
