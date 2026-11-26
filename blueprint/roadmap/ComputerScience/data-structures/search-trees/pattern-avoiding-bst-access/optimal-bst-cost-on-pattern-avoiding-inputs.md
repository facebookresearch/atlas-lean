# Pattern-avoiding inputs have linear optimal BST cost

For every fixed permutation $\pi$ there is a constant $c_\pi$ such that every $\pi$-avoiding permutation access sequence $X \in S_n$ has $\mathrm{OPT}(X) \le c_\pi\, n$. This resolves the pattern-avoidance conjecture of Chalermsook, Goswami, Kozma, Mehlhorn and Saranurak with a tight $O(1)$ amortized bound.

## Proof sketch

Berendsohn, Kozma and Opler construct an explicit offline arborally satisfied superset of size $O(n)$: they recursively decompose a $\pi$-avoiding permutation into a bounded number of blocks with simpler structure using the Marcus–Tardos theorem and the bounded grid-width of pattern-avoiding permutations, and serve each block by a tree whose shape follows the decomposition, so that each level of the recursion costs $O(n)$ in total and the number of levels is bounded in terms of $\pi$ only.

## Depends on

- [Pattern-avoidance conjecture for binary search trees](pattern-avoidance-conjecture.md)
- [Marcus–Tardos theorem on excluded permutation matrices](marcus-tardos-theorem.md)
- [Geometric characterization of the optimal offline BST cost](../geometric-view-of-bst-access/geometric-characterization-of-opt.md)

## Proof depends on

- [Pattern-avoidance conjecture for binary search trees](pattern-avoidance-conjecture.md)
- [Marcus–Tardos theorem on excluded permutation matrices](marcus-tardos-theorem.md)
- [Geometric characterization of the optimal offline BST cost](../geometric-view-of-bst-access/geometric-characterization-of-opt.md)

## Sources

- Benjamin Aram Berendsohn, László Kozma, Michal Opler, "Optimization with Pattern-Avoiding Input", STOC (2024), arXiv:2310.04236.
