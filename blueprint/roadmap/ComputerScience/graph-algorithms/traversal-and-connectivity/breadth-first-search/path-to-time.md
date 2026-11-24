# Cost of path reconstruction for a reachable vertex

Let $G$ be a finite directed graph
given by adjacency lists, let $s$ and $v$ be vertices, and suppose breadth-first search from $s$
reports distance $d$ for $v$. Following the saved parents of the breadth-first search forest of
$G$ from $s$ back from $v$ costs exactly $3d + 2$, counting one unit for each comparison with $s$,
each parent lookup and each vertex prepended to the path.
