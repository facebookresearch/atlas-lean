# Dijkstra's algorithm in priority-queue operations

Run Dijkstra's algorithm on a directed graph with $n$ vertices, $m$ arcs and nonnegative weights, as a client of an indexed minimum-priority queue on the vertices, a table of tentative distances and the adjacency lists. Independently of the queue implementation, it performs at most $n$ insertions, at most $n$ extract-min operations, at most $m$ decrease-key operations and $O(n + m)$ table and graph queries. Hence if an implementation charges (possibly amortized) costs $c_{\mathrm{ins}}$, $c_{\mathrm{ext}}$, $c_{\mathrm{dec}}$, the total cost is at most $n(c_{\mathrm{ins}} + c_{\mathrm{ext}}) + m\, c_{\mathrm{dec}} + O(n + m)$.

## Depends on

- [Dijkstra's finite distances are realized by walks](../dijkstra-s-algorithm/dijkstra-distance-realized.md)
- [Decrease-key in an indexed minimum queue](../../../data-structures/heaps/indexed-minimum-priority-queue/decrease-key.md)

## Sources

- E. W. Dijkstra, "A Note on Two Problems in Connexion with Graphs", Numerische Mathematik 1, 1959.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
