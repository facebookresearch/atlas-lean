# Each reachable vertex has a unique saved-parent chain

Let $G$ be a finite directed graph
given by adjacency lists, and let $s$ and $v$ be vertices with $v$ reachable from $s$ in $G$.
There is exactly one list of vertices that starts at $s$, ends at $v$, and in which each vertex
after the first has the preceding vertex as its saved parent in the breadth-first search forest
of $G$ from $s$.
