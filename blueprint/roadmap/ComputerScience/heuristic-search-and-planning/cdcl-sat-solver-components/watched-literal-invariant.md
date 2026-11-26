# Completeness of propagation with two watched literals

Maintain the invariant that for every clause $C$ with watches $\ell_1, \ell_2$, if $\ell_1$ is false under the trail $M$ then either $\ell_2$ is true at a decision level no higher than that of $\ell_1$, or every literal of $C$ other than the watches is false at a decision level no higher than that of $\ell_1$. Then after all queued trail literals have been processed, no clause of the database is unit or falsified under $M$ unless the scheme has reported it. Hence propagation with two watched literals finds exactly the unit clauses and conflicts that a full scan of the database would find, while visiting only the watch lists of newly falsified literals; backjumping to a lower decision level preserves the invariant without any watch updates.

## Proof sketch

A clause can become unit or false only when one of its watches becomes false, at which moment the clause is on that literal's watch list and is examined. Backjumping to level $b$ keeps every assignment of level at most $b$, so if $\ell_1$ stays false, the literals the invariant names keep their values.

## Depends on

- [Two-watched-literal scheme](two-watched-literal-scheme.md)

## Sources

- M. W. Moskewicz, C. F. Madigan, Y. Zhao, L. Zhang and S. Malik, "Chaff: Engineering an Efficient SAT Solver", Proceedings of the 38th Design Automation Conference, 2001.
- N. Eén and N. Sörensson, "An Extensible SAT-solver", Theory and Applications of Satisfiability Testing (SAT 2003), LNCS 2919, Springer, 2004.
