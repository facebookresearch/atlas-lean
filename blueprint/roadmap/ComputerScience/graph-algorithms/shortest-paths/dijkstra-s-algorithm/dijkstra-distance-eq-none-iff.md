# Dijkstra's distance is infinite exactly at unreachable vertices

Let $G$ be a directed
graph on the vertices $0, \dots, n-1$, let $w(u, v)$ be a natural-number weight for every
ordered pair of vertices, and let $s$ and $t$ be vertices. The distance to $t$ output by
Dijkstra's algorithm on $G$ with weights $w$ from source $s$ is infinite if and only if $t$ is
not reachable from $s$ in $G$.
