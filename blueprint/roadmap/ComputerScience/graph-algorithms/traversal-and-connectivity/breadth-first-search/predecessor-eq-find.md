# The BFS parent is the first discovered in-neighbour

Let $G$ be a finite directed graph
with ordered adjacency lists, $s$ a vertex, and $F$ the predecessor forest computed by
breadth-first search with parents from $s$ in $G$. For every vertex $v \ne s$, the predecessor
that $F$ records for $v$ is the first vertex $u$, in the first-discovery order of ordinary FIFO
breadth-first search from $s$ in $G$, whose adjacency list contains $v$; if no vertex in that
order has $v$ in its adjacency list, $F$ records no predecessor for $v$.
