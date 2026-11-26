# Size upper bound for DPLL refutations

On an unsatisfiable CNF formula with $N$ variables, the search tree of the trail-based DPLL search branches on each variable at most once along every root-to-leaf path, so it has at most $2^N$ leaves, and the tree-like resolution refutation and LRAT certificate it produces have size at most $2^{N+1} - 1$ lines (plus the input clauses).

## Proof sketch

The search branches only on unassigned variables, so every path has depth at most $N$; a binary tree of depth $N$ has fewer than $2^{N+1}$ nodes.

## Depends on

- [DPLL search with an explicit trail](dpll-explicit-trail-search.md)
- [Tree-like resolution derivation](../../../Logic/propositional-logic/resolution-size-and-width/resolution-tree.md)

## Sources

- M. Davis, G. Logemann and D. Loveland, "A Machine Program for Theorem-Proving", Communications of the ACM 5(7), 1962.
- O. Beyersdorff, N. Galesi and M. Lauria, "A Lower Bound for the Pigeonhole Principle in Tree-like Resolution by Asymmetric Prover-Delayer Games", Information Processing Letters 110(23), 2010.
