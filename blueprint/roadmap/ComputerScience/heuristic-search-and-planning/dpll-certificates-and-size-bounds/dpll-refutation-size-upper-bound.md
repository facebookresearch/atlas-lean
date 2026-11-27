# Size upper bound for DPLL refutations

On an unsatisfiable CNF formula with $N$ variables, the search tree of the trail-based DPLL search branches on each variable at most once along every root-to-leaf path, so it has at most $2^N$ leaves. The tree-like resolution refutation read off it has at most $2^{N+1} - 1$ clauses (input clauses at the leaves included), and the LRAT certificate the solver produces has at most $2^N - 1$ addition steps.

## Proof sketch

Branchings and unit propagations assign only unassigned variables, so every path has at most $N$ inner nodes. Counting each unit propagation as a branching whose other child is a leaf falsifying the unit clause gives a binary tree of depth at most $N$, with at most $2^N$ leaves and fewer than $2^{N+1}$ nodes; the refutation has no more clauses than this tree has nodes, and one addition step per inner node.

## Depends on

- [DPLL search with an explicit trail](dpll-explicit-trail-search.md)
- [Tree-like resolution derivation](../../../Logic/propositional-logic/resolution-size-and-width/resolution-tree.md)
- [A DPLL solver that emits LRAT certificates](dpll-solver-with-lrat-certificates.md)

## Proof depends on

- [Failing DPLL search trees give tree-like resolution refutations](../../../Logic/propositional-logic/sat-solving/failing-dpll-search-trees-give-tree-like.md)

## Sources

- M. Davis, G. Logemann and D. Loveland, "A Machine Program for Theorem-Proving", Communications of the ACM 5(7), 1962.
- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT Modulo Theories: From an Abstract Davis-Putnam-Logemann-Loveland Procedure to DPLL(T)", Journal of the ACM 53(6), 2006.
