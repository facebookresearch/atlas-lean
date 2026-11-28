# $O(\log\log n)$-competitive search trees on trees

For every tree $G$ on $n$ vertices there is an online dynamic search tree on $G$, the *Tango search tree*, whose cost on every search sequence of length $m = \Omega(n)$ is $O(\log\log n)$ times the cost of the optimal offline dynamic search tree on $G$ for that sequence. This matches the best competitive ratio known for binary search trees, the case where $G$ is a path.

## Proof sketch

Bose, Cardinal, Iacono, Koumoutsos and Langerman first generalize the interleave lower bound to search trees on trees, with respect to a fixed reference search tree on $G$, and then follow the Tango paradigm of paying $O(\log\log n)$ per unit increase of that bound. Since a preferred path of vertices of $G$ cannot simply be stored in a red-black tree, they introduce *Steiner-closed* search trees, in which the vertices on every root path form a Steiner-closed set of $G$, and use a two-level decomposition, first from $G$ into Steiner-closed trees and then from these into paths, maintained with link-cut trees.

## Depends on

- [Search trees on trees](search-trees-on-trees.md)

## Proof depends on

- [Link-cut trees take logarithmic amortized time](../../disjoint-sets-and-dynamic-trees/link-cut-tree/link-cut-trees-take-logarithmic-amortized-time.md)

## Sources

- Prosenjit Bose, Jean Cardinal, John Iacono, Grigorios Koumoutsos, Stefan Langerman, "Competitive Online Search Trees on Trees", SODA (2020); ACM Transactions on Algorithms 19(3) (2023), arXiv:1908.00848.
