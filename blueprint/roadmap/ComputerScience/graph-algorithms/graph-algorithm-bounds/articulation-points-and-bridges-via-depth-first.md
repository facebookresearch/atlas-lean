# Articulation points and bridges via depth-first search

Let $G$ be an undirected graph and run depth-first search, assigning discovery times $\mathrm{disc}(u)$ and low values $\mathrm{low}(u)$, the least discovery time reachable from the subtree of $u$ using at most one back edge. A non-root vertex $u$ is an articulation point if and only if it has a child $v$ in the DFS tree with $\mathrm{low}(v) \ge \mathrm{disc}(u)$; the root is an articulation point if and only if it has at least two children. A tree edge $(u, v)$ is a bridge if and only if $\mathrm{low}(v) > \mathrm{disc}(u)$, and no back edge is a bridge. All articulation points, bridges and biconnected components are computed in $O(|V| + |E|)$ time.

## Proof depends on

- [Left-first depth-first search](../traversal-and-connectivity/depth-first-search/dfs.md)

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 4th ed., MIT Press, 2022
- R. E. Tarjan, "Depth-first search and linear graph algorithms", *SIAM Journal on Computing* 1(2):146–160, 1972
