# Tovey: exact 3-CNF formulas with at most three occurrences per variable are satisfiable

Let $\varphi$ be a CNF formula in which every clause contains exactly three literals on three pairwise distinct variables, and every variable occurs in at most three clauses (counting repeated clauses separately). Then $\varphi$ is satisfiable. In contrast, satisfiability of 3-CNF formulas with at most four occurrences per variable is NP-complete, so three occurrences mark the tractable boundary.

## Proof sketch

Consider the bipartite incidence graph between clauses and variables. Every set $S$ of clauses has $3|S|$ incidences, and each variable absorbs at most three, so $|N(S)| \ge |S|$; by Hall's theorem there is a system of distinct representative variables. Setting each representative to satisfy its own clause is consistent because representatives are distinct.

## Depends on

- [Satisfiability of a CNF formula](../../conjunctive-normal-form/cnfsat.md)

## Sources

- C. A. Tovey, "A Simplified NP-Complete Satisfiability Problem", Discrete Applied Mathematics 8(1), 85–89, 1984: Theorem 2.3 (3,4-SAT is NP-complete) and Theorem 2.4 (every 3,3-SAT instance is satisfiable).
- P. Berman, M. Karpinski and A. D. Scott, "Computational Complexity of Some Restricted Instances of 3-SAT", Discrete Applied Mathematics 155(5), 649–653, 2007.
