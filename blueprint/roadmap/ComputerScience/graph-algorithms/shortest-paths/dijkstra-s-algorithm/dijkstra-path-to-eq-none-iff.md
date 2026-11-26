# Dijkstra's path reconstruction fails exactly at infinite distance

Let $G$ be a directed
graph on the vertices $0, \dots, n-1$, let $w(u, v)$ be a natural-number weight for every
ordered pair of vertices, and let $s$ and $t$ be vertices. Reconstructing a path from $s$ to
$t$ by following, for at most $n$ steps, the predecessor pointers output by Dijkstra's
algorithm on $G$ with weights $w$ from source $s$ fails if and only if the distance output
for $t$ is infinite.
