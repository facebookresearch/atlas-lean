# Hierholzer's algorithm

Let $G$ be a directed adjacency graph, read as a multigraph with
one edge occurrence per adjacency entry, let $s$ be a vertex, and let $m$ be the number of edge
occurrences of $G$, that is, the length of its edge list. Hierholzer's algorithm on $G$ from $s$
runs Hierholzer's recursion from $s$ with fuel $m + 1$, with the adjacency list of each vertex as
its list of remaining out-neighbours and the empty list as accumulator, and returns the list of
vertices produced by the recursion, at the cost of the recursion.
