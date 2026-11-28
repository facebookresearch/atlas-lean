# PLS reduction and tight PLS reduction

A PLS reduction from a local search problem $P$ to a local search problem $Q$ is a pair of polynomial-time maps $(\phi, \psi)$: $\phi$ maps instances $I$ of $P$ to instances $\phi(I)$ of $Q$, and for every instance $I$, $\psi(I, \cdot) : F_Q(\phi(I)) \to F_P(I)$ maps every feasible solution of $\phi(I)$ to a feasible solution of $I$, such that $\psi(I, s)$ is a local optimum of $I$ whenever $s$ is a local optimum of $\phi(I)$; here $F_P(I)$ denotes the set of feasible solutions of $I$. It is tight if for every instance $I$ there is a set $\mathcal{R}$ of feasible solutions of $\phi(I)$ containing all its local optima such that $\psi(I, \cdot)$ maps $\mathcal{R}$ onto solutions of $I$ (for every solution $p$ of $I$ some $q \in \mathcal{R}$ with $\psi(I, q) = p$ can be constructed in polynomial time) and every improving path of $\phi(I)$ that starts in $\mathcal{R}$, ends in $\mathcal{R}$ and has interior outside $\mathcal{R}$ is mapped to an improving path of length at most one (a single step or no step) of $I$. Tight reductions transfer exponential lower bounds on improving paths and PSPACE-completeness of the standard algorithm problem.

## Depends on

- [The class PLS of polynomial local search problems](../../../../TheoryOfComputation/complexity-classes/total-search-problems/the-class-pls-of-polynomial-local-search.md)

## Sources

- D. S. Johnson, C. H. Papadimitriou, M. Yannakakis, "How easy is local search?", Journal of Computer and System Sciences 37(1) (1988).
- A. A. Schäffer, M. Yannakakis, "Simple Local Search Problems that are Hard to Solve", SIAM Journal on Computing 20(1) (1991).
