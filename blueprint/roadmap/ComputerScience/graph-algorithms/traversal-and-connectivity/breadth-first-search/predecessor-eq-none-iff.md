# Exactly the source and the unreachable vertices have no BFS parent

Let $G$ be a finite
directed graph with ordered adjacency lists, $s$ a vertex, and $F$ the predecessor forest
computed by breadth-first search with parents from $s$ in $G$. A vertex $v$ has no recorded
predecessor in $F$ if and only if $v = s$ or $v$ is not reachable from $s$ along directed edges
of $G$.
