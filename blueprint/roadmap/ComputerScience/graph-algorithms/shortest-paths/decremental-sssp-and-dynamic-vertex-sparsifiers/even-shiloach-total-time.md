# Even-Shiloach: exact decremental BFS trees in O(mD) total update time

An Even-Shiloach tree of depth $D$ on an unweighted undirected graph with $m$ edges maintains exact distances $\mathrm{dist}_G(s, v)$ for all $v$ with $\mathrm{dist}_G(s, v) \le D$, and a shortest path tree on them, over any sequence of edge deletions, in total time $O(mD)$, with $O(1)$ distance queries. With $D = n$ this gives deterministic exact decremental SSSP in total time $O(mn)$ for unweighted undirected graphs; being deterministic, it works against adaptive adversaries.

## Proof sketch

Edge deletions only increase distances, so every level $\ell(v)$ is nondecreasing and takes at most $D + 1$ finite values. Between two increases of $\ell(v)$, the scan pointer of $v$ moves monotonically through its $\deg(v)$ neighbours, because a neighbour rejected at level $\ell(v) - 1$ can never return to that level. Thus $v$ costs $O(\deg(v))$ per level, and summing over vertices and levels gives $O(D \sum_v \deg(v)) = O(mD)$.

## Depends on

- [Even-Shiloach trees of bounded depth](even-shiloach-tree.md)

## Proof depends on

- [Reconstructed BFS paths are shortest paths](../../traversal-and-connectivity/breadth-first-search/path-to-spec.md)

## Sources

- Shimon Even, Yossi Shiloach, "An On-Line Edge-Deletion Problem", J. ACM 28(1) (1981).
