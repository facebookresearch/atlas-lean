# $O(\log\log n)$-competitive search trees on trees

For every tree $G$ on $n$ vertices there is an online dynamic search tree on $G$ whose cost on every access sequence is $O(\log\log n)$ times the cost of the optimal offline dynamic search tree on $G$ for that sequence, plus $O(n)$. This extends the tango-tree guarantee from paths to arbitrary trees.

## Proof sketch

Decompose $G$ by a heavy-path style centroid decomposition into a structure of depth $O(\log n)$ playing the role of the reference tree, prove a Wilber-type interleave lower bound for search trees on trees with respect to this decomposition, and maintain preferred paths with auxiliary structures whose operations cost $O(\log\log n)$.

## Depends on

- [Search trees on trees](search-trees-on-trees.md)
- [Tango trees are $O(\log\log n)$-competitive](tango-competitiveness.md)

## Proof depends on

- [Search trees on trees](search-trees-on-trees.md)
- [Tango trees are $O(\log\log n)$-competitive](tango-competitiveness.md)

## Sources

- Prosenjit Bose, Jean Cardinal, John Iacono, Grigorios Koumoutsos, Stefan Langerman, "Competitive Online Search Trees on Trees", SODA (2020); ACM Transactions on Algorithms 19(3) (2023), arXiv:1908.00848.
