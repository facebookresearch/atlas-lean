# DPLL refutations of pigeonhole formulas are exponential

Let $\mathrm{PHP}^{n+1}_n$ be the CNF formula stating that $n+1$ pigeons are mapped injectively into $n$ holes (variables $p_{ij}$, clauses $\bigvee_j p_{ij}$ for every pigeon $i$, and $\neg p_{ij} \vee \neg p_{i'j}$ for $i \ne i'$). For even $n \ge 2$, every tree-like resolution refutation of $\mathrm{PHP}^{n+1}_n$ has at least $2^{(n/2)\log_2(n/2 + 1)}$ clauses; hence for every $n \ge 2$ it has at least $2^{\lfloor n/2 \rfloor}$ clauses, and the size is $2^{\Omega(n \log n)}$. Consequently, for every numbering of the variables, the tree-like refutation read off the failing search tree of the DPLL solver on $\mathrm{PHP}^{n+1}_n$ has at least $2^{\lfloor n/2 \rfloor}$ clauses, the LRAT certificate the solver returns has at least $2^{\lfloor n/2 \rfloor - 1}$ addition steps, and the search tree has at least $2^{\lfloor n/2 \rfloor}/(2N + 2)$ leaves, where $N = n(n+1)$.

## Proof sketch

A tree-like refutation is a decision tree that finds a falsified clause on every assignment. In the asymmetric Prover-Delayer game, Delayer scores $\log_2 c_b$ points when she lets Prover set a variable to $b$, with $1/c_0 + 1/c_1 = 1$, and a refutation of size $S$ limits her to $\log_2 S$ points. For the pigeonhole formulas, $c_1 = n/2 + 1 - p$ and $c_0 = (n/2 + 1 - p)/(n/2 - p)$, where $p$ counts the free holes already excluded for the pigeon queried; Delayer never violates a hole clause and earns $\log_2(n/2 + 1)$ points on each of at least $n/2$ pigeons. Odd $n$ reduces to $n - 1$ by placing the last pigeon in the last hole, which restricts a refutation to one of $\mathrm{PHP}^{n}_{n-1}$ of no larger size. The consequences use one addition step per inner node of the refutation and the bound of at most $2s(N+1) - 1$ clauses for the refutation read off a search tree with $s$ leaves.

## Depends on

- [A DPLL solver that emits LRAT certificates](dpll-solver-with-lrat-certificates.md)
- [Tree-like resolution derivation](../../../Logic/propositional-logic/resolution-size-and-width/resolution-tree.md)

## Proof depends on

- [Failing DPLL search trees give tree-like resolution refutations](../../../Logic/propositional-logic/sat-solving/failing-dpll-search-trees-give-tree-like.md)

## Sources

- O. Beyersdorff, N. Galesi and M. Lauria, "A Lower Bound for the Pigeonhole Principle in Tree-like Resolution by Asymmetric Prover-Delayer Games", Information Processing Letters 110(23), 2010, Theorems 1 and 2.
- M. Davis, G. Logemann and D. Loveland, "A Machine Program for Theorem-Proving", Communications of the ACM 5(7), 1962.
