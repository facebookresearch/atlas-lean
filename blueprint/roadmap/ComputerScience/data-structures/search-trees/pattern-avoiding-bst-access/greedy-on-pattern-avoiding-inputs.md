# Greedy on pattern-avoiding access sequences

For every fixed $\pi \in S_k$, geometric Greedy serves every $\pi$-avoiding permutation access sequence $X \in S_n$, from an arbitrary initial tree, with total cost at most $n \cdot 2^{\alpha(n)^{O(k)}}$, where $\alpha$ is the inverse Ackermann function; in particular preorder sequences, which avoid $231$, cost $n \cdot 2^{\alpha(n)^{O(1)}}$. Chalermsook, Pettie and Yingchareonthawornchai improved the general bound to $n \cdot 2^{O(k^2) + (1+o(1))\alpha(n)}$.

## Proof sketch

Greedy is *input-revealing*: its execution log partially reveals the structure of the access sequence, so the matrix of points Greedy touches avoids a forbidden pattern derived from $\pi$. Its number of ones is therefore bounded by an extremal function of $0$-$1$ matrices, estimated with the Marcus–Tardos theorem for permutation patterns and with Nivasch's and Pettie's bounds for light patterns, which yields the inverse-Ackermann-type bound. The improvement bounds the extremal function of the Kronecker product of the permutation matrix of $\pi$ with a fixed three-entry pattern, the quantity that controls this argument, nearly tightly.

## Depends on

- [Geometric Greedy (Greedy Future)](../geometric-view-of-bst-access/geometric-greedy.md)
- [Inverse Ackermann function of Tarjan and van Leeuwen](../../disjoint-sets-and-dynamic-trees/disjoint-set-data-structure/inverse-ackermann-tv-l.md)
- [Classical pattern containment in a sequence](../../../../Combinatorics/permutations/permutation-patterns/cyclic-pattern-avoiding-stack-sorting/contains-pattern-seq.md)

## Proof depends on

- [Marcus–Tardos theorem on excluded permutation matrices](marcus-tardos-theorem.md)

## Sources

- Parinya Chalermsook, Mayank Goswami, László Kozma, Kurt Mehlhorn, Thatchaphol Saranurak, "Pattern-Avoiding Access in Binary Search Trees", FOCS (2015), arXiv:1507.06953.
- Parinya Chalermsook, Seth Pettie, Sorrachai Yingchareonthawornchai, "Sorting Pattern-Avoiding Permutations via 0-1 Matrices Forbidding Product Patterns", SODA (2024), arXiv:2307.02294.
- Benjamin Aram Berendsohn, László Kozma, Michal Opler, "Optimization with Pattern-Avoiding Input", STOC (2024), arXiv:2310.04236.
