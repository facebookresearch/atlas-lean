# Local Max-Cut under the flip neighbourhood is PLS-complete

The local search problem Local Max-Cut asks, given an undirected graph with integer edge weights, for a cut $(S, V \setminus S)$ such that moving any single vertex to the other side does not increase the total weight of cut edges. Local Max-Cut is PLS-complete under tight PLS reductions. Consequently there are instances and starting cuts from which every sequence of improving flips has exponential length, and computing the local optimum reached by the standard greedy local search from a given cut is PSPACE-complete.

## Proof sketch

Reduce from a PLS-complete circuit local search problem (Flip for Boolean circuits) through a chain of tight reductions: first to weighted satisfiability problems with the flip neighbourhood (positive not-all-equal 2-SAT), whose clauses directly translate into weighted edges between vertices representing variables. Tightness of each step preserves exponential improving paths and the PSPACE-completeness of the standard algorithm problem.

## Depends on

- [PLS reduction and tight PLS reduction](pls-reduction-and-tight-reduction.md)
- [MAX-CUT as an optimization problem](../../../../TheoryOfComputation/pcp-and-inapproximability/inapproximability-of-max-cut/max-cut.md)
- [The class PLS of polynomial local search problems](../../../../TheoryOfComputation/complexity-classes/total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Sources

- A. A. Schäffer, M. Yannakakis, "Simple Local Search Problems that are Hard to Solve", SIAM Journal on Computing 20(1) (1991).
- D. S. Johnson, C. H. Papadimitriou, M. Yannakakis, "How easy is local search?", Journal of Computer and System Sciences 37(1) (1988).
