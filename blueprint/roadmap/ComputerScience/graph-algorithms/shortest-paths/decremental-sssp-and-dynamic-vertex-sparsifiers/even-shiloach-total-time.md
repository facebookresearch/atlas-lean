# Even-Shiloach: exact decremental BFS trees in O(mD) total update time

An Even-Shiloach tree of depth $D$ on an unweighted undirected graph with $m$ edges maintains exact distances $\mathrm{dist}_G(s, v)$ for all $v$ with $\mathrm{dist}_G(s, v) \le D$, and a shortest path tree on them, over any sequence of edge deletions, in total time $O(mD)$, with $O(1)$ distance queries. With $D = n$ this gives deterministic exact decremental SSSP in total time $O(mn)$ for unweighted undirected graphs; being deterministic, it works against adaptive adversaries.

## Proof sketch

Edge deletions only increase distances, so every level $\ell(v)$ is nondecreasing and takes at most $D + 1$ finite values. Use the heap-free scan-pointer implementation of the Even-Shiloach tree. Between two increases of $\ell(v)$, the scan pointer of $v$ moves monotonically through its $\deg(v)$ neighbours, because a neighbour rejected at level $\ell(v) - 1$ can never return to that level. Each increase of $\ell(v)$ also notifies the $\deg(v)$ neighbours of $v$. Thus $v$ costs $O(\deg(v))$ per level, and summing over vertices and levels gives $O(D \sum_v \deg(v)) = O(mD)$.

## Depends on

- [Even-Shiloach trees of bounded depth](even-shiloach-tree.md)
- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)

## Proof depends on

- [Reconstructed BFS paths are shortest paths](../../traversal-and-connectivity/breadth-first-search/path-to-spec.md)

## Sources

- Shimon Even, Yossi Shiloach, "An On-Line Edge-Deletion Problem", J. ACM 28(1) (1981).
- Monika Henzinger, Sebastian Krinninger, Danupon Nanongkai, "Dynamic Approximate All-Pairs Shortest Paths: Breaking the O(mn) Barrier and Derandomization", FOCS (2013); SIAM Journal on Computing (2016), arXiv:1308.0776, Section 2.2.
- Valerie King, "Fully Dynamic Algorithms for Maintaining All-Pairs Shortest Paths and Transitive Closure in Digraphs", FOCS (1999).
