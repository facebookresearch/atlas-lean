# Cost of path reconstruction for an unreachable vertex

Let $G$ be a finite directed graph
given by adjacency lists, and let $s$ and $v$ be vertices with $v$ not reachable from $s$ in $G$.
Following the saved parents of the breadth-first search forest of $G$ from $s$ back from $v$ costs
exactly $2$, counting one unit for each comparison with $s$, each parent lookup and each vertex
prepended to the path: one comparison of $v$ with $s$ and one lookup of the missing parent of
$v$.
