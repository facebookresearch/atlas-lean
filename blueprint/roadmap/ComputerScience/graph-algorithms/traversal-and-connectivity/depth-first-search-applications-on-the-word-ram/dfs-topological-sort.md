# Reverse DFS finishing order is a topological order exactly for acyclic graphs

Let $G$ be a finite directed graph given by adjacency lists, and let $\pi$ be the list of all vertices in decreasing order of finishing time of a depth-first search of the whole graph. Then $\pi$ is a topological order of $G$ (every edge goes from an earlier to a later vertex) if and only if $G$ is acyclic. In particular $G$ is acyclic if and only if it has a topological order.

## Proof sketch

For an edge $u \to v$ in an acyclic graph, $v$ finishes before $u$ in every case of the parenthesis theorem (descendant, already finished, or cross edge). A back edge, which must exist in any cycle, violates the order.

## Depends on

- [Topological order](../topological-sorting/is-topological-order.md)
- [Acyclic directed graph](../topological-sorting/is-acyclic.md)
- [Whole-graph decreasing finish order](../depth-first-search/decreasing-finish-all.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
- R. E. Tarjan, "Depth-First Search and Linear Graph Algorithms", SIAM Journal on Computing 1(2), 1972.
