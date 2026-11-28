# Even-Shiloach trees of bounded depth

Let $G = (V, E)$ be an unweighted undirected graph undergoing edge deletions, $s \in V$ and $D \in \mathbb{N}$. An *Even-Shiloach tree* of depth $D$ rooted at $s$ stores, for every $v \in V$, a level $\ell(v) = \mathrm{dist}_G(s, v)$ if this is at most $D$ and $\ell(v) = \infty$ otherwise, and, for every $v$ with $1 \le \ell(v) \le D$ (so not for the root $s$, nor for vertices beyond the cutoff), a parent $p(v)$, a neighbour with $\ell(p(v)) = \ell(v) - 1$. After an edge deletion, its endpoints are examined; an examined vertex $v \ne s$ computes $\ell'(v) = \min_u (\ell(u) + 1)$ over its current neighbours $u$, and if $\ell'(v) > \ell(v)$ it raises its level to $\ell'(v)$, or to $\infty$ (with no parent) if $\ell'(v) > D$, and notifies all its neighbours, which are examined in turn, until no level changes; a vertex with a finite level takes as parent a neighbour attaining the minimum. Keeping each vertex's neighbours in a heap keyed by level costs an extra $\log n$ factor; King (1999) explains how to avoid heaps in unweighted graphs. One heap-free implementation gives each vertex $v$ a pointer into its neighbour list marking how far it has scanned for a neighbour at level $\ell(v) - 1$: when $v$ loses its parent it advances the pointer to the next such neighbour, and if none remains it increases $\ell(v)$ by one and rescans from the start, which reaches the same level $\ell'(v)$.

## Depends on

- [Breadth-first search](../../traversal-and-connectivity/breadth-first-search/bfs.md)

## Sources

- Shimon Even, Yossi Shiloach, "An On-Line Edge-Deletion Problem", J. ACM 28(1) (1981).
- Monika Henzinger, Sebastian Krinninger, Danupon Nanongkai, "Decremental Single-Source Shortest Paths on Undirected Graphs in Near-Linear Total Update Time", FOCS (2014); J. ACM 65(6) (2018), arXiv:1512.08148.
- Monika Henzinger, Sebastian Krinninger, Danupon Nanongkai, "Dynamic Approximate All-Pairs Shortest Paths: Breaking the O(mn) Barrier and Derandomization", FOCS (2013); SIAM Journal on Computing (2016), arXiv:1308.0776, Section 2.2 (Algorithm 1, the Even-Shiloach tree with heaps, and the remark crediting King with avoiding heaps).
- Valerie King, "Fully Dynamic Algorithms for Maintaining All-Pairs Shortest Paths and Transitive Closure in Digraphs", FOCS (1999).
