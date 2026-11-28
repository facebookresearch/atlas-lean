# Pattern-avoiding inputs have linear optimal BST cost

For every fixed permutation $\pi$ of size $k$ there is a constant $c_\pi = 2^{O(k)}$ such that every $\pi$-avoiding permutation access sequence $X \in S_n$ has $\mathrm{OPT}(X) \le c_\pi\, n$; more generally, every access sequence of length $m$ avoiding $\pi$ can be served with total cost $2^{O(k)} m$. This resolves the pattern-avoidance conjecture of Chalermsook, Goswami, Kozma, Mehlhorn and Saranurak with a tight $O(1)$ amortized bound.

## Proof sketch

Berendsohn, Kozma and Opler construct an offline solution, in the arborally satisfied superset view, from the merge-sequence decomposition of permutations of Guillemot and Marx that underlies twin-width. Following a merge sequence of width $d$, they serve the access sequence with cost $O(n d^2)$. A permutation avoiding a pattern of size $k$ has twin-width $2^{O(k)}$ by the Guillemot–Marx theorem with Fox's improvement, which rests on the Marcus–Tardos theorem, and this gives the bound.

## Depends on

- [Pattern-avoidance conjecture for binary search trees](pattern-avoidance-conjecture.md)
- [Classical pattern containment in a sequence](../../../../Combinatorics/permutations/permutation-patterns/cyclic-pattern-avoiding-stack-sorting/contains-pattern-seq.md)
- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Proof depends on

- [Marcus–Tardos theorem on excluded permutation matrices](marcus-tardos-theorem.md)
- [Geometric characterization of the optimal offline BST cost](../geometric-view-of-bst-access/geometric-characterization-of-opt.md)

## Sources

- Benjamin Aram Berendsohn, László Kozma, Michal Opler, "Optimization with Pattern-Avoiding Input", STOC (2024), arXiv:2310.04236.
