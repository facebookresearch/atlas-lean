# Even-Shiloach trees of bounded depth

Let $G = (V, E)$ be an unweighted undirected graph undergoing edge deletions, $s \in V$ and $D \in \mathbb{N}$. An *Even-Shiloach tree* of depth $D$ rooted at $s$ stores, for every $v \in V$, a level $\ell(v) = \mathrm{dist}_G(s, v)$ if this is at most $D$ and $\ell(v) = \infty$ otherwise, and, for every $v$ with $1 \le \ell(v) \le D$ (so not for the root $s$, nor for vertices beyond the cutoff), a parent $p(v)$, a neighbour with $\ell(p(v)) = \ell(v) - 1$, and a pointer into the neighbour list of $v$ marking how far $v$ has scanned. After a deletion, every vertex that loses its parent advances its pointer to the next neighbour $u$ with $\ell(u) = \ell(v) - 1$; if none remains, it increases $\ell(v)$ by one, rescans from the start, and notifies its children, repeating until all levels are consistent; a vertex whose level would exceed $D$ gets $\ell(v) = \infty$ and no parent.

## Depends on

- [Breadth-first search](../../traversal-and-connectivity/breadth-first-search/bfs.md)

## Sources

- Shimon Even, Yossi Shiloach, "An On-Line Edge-Deletion Problem", J. ACM 28(1) (1981).
- Monika Henzinger, Sebastian Krinninger, Danupon Nanongkai, "Decremental Single-Source Shortest Paths on Undirected Graphs in Near-Linear Total Update Time", FOCS (2014); J. ACM 65(6) (2018), arXiv:1512.08148.
