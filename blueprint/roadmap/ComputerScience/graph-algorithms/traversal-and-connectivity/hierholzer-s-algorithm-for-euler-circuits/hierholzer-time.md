# Running time of Hierholzer's algorithm

Let $G$ be a directed adjacency graph, read as a
multigraph with one edge per adjacency entry, and let $s$ and $t$ be vertices such that $G$ is
semi-balanced for $s$ and $t$ and the source of every edge of $G$ is reachable from $s$. Then
Hierholzer's algorithm on $G$ from $s$ costs exactly $|E|$ units, where $|E|$ is the number of
edge occurrences of $G$, that is, the length of its edge list.

The cost model charges one unit per edge traversal (removing the head of an adjacency list);
reading an adjacency list and emitting a vertex are free.
