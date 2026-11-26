# Greedy on pattern-avoiding access sequences

For every fixed $\pi \in S_k$, geometric Greedy serves every $\pi$-avoiding permutation access sequence $X \in S_n$ with cost $n \cdot 2^{\alpha(n)^{c_\pi}}$ for a constant $c_\pi$ depending only on $\pi$, where $\alpha$ is the inverse Ackermann function. Chalermsook, Pettie and Yingchareonthawornchai improved the general bound to $n \cdot 2^{(1+o(1))\alpha(n)}$.

## Proof sketch

The geometric Greedy output on a $\pi$-avoiding input avoids a related forbidden configuration, so its size is an extremal function of $0$-$1$ matrices forbidding a fixed light pattern. Such extremal functions are bounded via generalized Davenport–Schinzel sequence estimates and the Marcus–Tardos theorem, yielding the inverse-Ackermann-type bounds; the improvement decomposes the forbidden patterns as products and applies a sharper sequence bound.

## Depends on

- [Pattern-avoidance conjecture for binary search trees](pattern-avoidance-conjecture.md)
- [Marcus–Tardos theorem on excluded permutation matrices](marcus-tardos-theorem.md)
- [Geometric Greedy (Greedy Future)](../geometric-view-of-bst-access/geometric-greedy.md)
- [Inverse Ackermann function of Tarjan and van Leeuwen](../../disjoint-sets-and-dynamic-trees/disjoint-set-data-structure/inverse-ackermann-tv-l.md)

## Proof depends on

- [Pattern-avoidance conjecture for binary search trees](pattern-avoidance-conjecture.md)
- [Marcus–Tardos theorem on excluded permutation matrices](marcus-tardos-theorem.md)
- [Geometric Greedy (Greedy Future)](../geometric-view-of-bst-access/geometric-greedy.md)
- [Inverse Ackermann function of Tarjan and van Leeuwen](../../disjoint-sets-and-dynamic-trees/disjoint-set-data-structure/inverse-ackermann-tv-l.md)

## Sources

- Parinya Chalermsook, Mayank Goswami, László Kozma, Kurt Mehlhorn, Thatchaphol Saranurak, "Pattern-Avoiding Access in Binary Search Trees", FOCS (2015), arXiv:1507.06953.
- Parinya Chalermsook, Seth Pettie, Sorrachai Yingchareonthawornchai, "Sorting Pattern-Avoiding Permutations via 0-1 Matrices Forbidding Product Patterns", SODA (2024), arXiv:2307.02294.
