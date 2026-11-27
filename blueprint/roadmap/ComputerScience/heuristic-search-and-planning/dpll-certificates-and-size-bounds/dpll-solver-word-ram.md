# The DPLL solver on the word RAM

There is a deterministic word-RAM program that on the encoding of a CNF formula $\varphi$ of length $E$ whose variables are below $N$ returns the same answer as the trail-based DPLL solver: $[0]$ when $\varphi$ is unsatisfiable, and $1$ followed by the bits of a satisfying assignment otherwise. Each step of the trail search is performed by one scan over the clauses in $O(E + N)$ instructions, and the number of steps is at most $2^{N+1}$, so the running time is $O\big(2^{N}(E + N)\big)$. On $\mathrm{PHP}^{n+1}_n$, for every numbering of the variables, the search performs $2^{\Omega(n \log n)}$ steps, so the running time is $2^{\Omega(n \log n)}$.

## Proof sketch

One iteration of the main loop rewrites the trail stored as a literal array and an entry stack exactly as one search step; the step count is bounded by the number of search-tree nodes. Each step creates at most one node, and on the pigeonhole formulas the search tree has $2^{\Omega(n \log n)}$ nodes.

## Depends on

- [DPLL search with an explicit trail](dpll-explicit-trail-search.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Size upper bound for DPLL refutations](dpll-refutation-size-upper-bound.md)
- [DPLL refutations of pigeonhole formulas are exponential](dpll-pigeonhole-refutation-lower-bound.md)

## Sources

- M. Davis, G. Logemann and D. Loveland, "A Machine Program for Theorem-Proving", Communications of the ACM 5(7), 1962.
- O. Beyersdorff, N. Galesi and M. Lauria, "A Lower Bound for the Pigeonhole Principle in Tree-like Resolution by Asymmetric Prover-Delayer Games", Information Processing Letters 110(23), 2010.
