# Dijkstra's predecessor pointers satisfy the distance equation

Let $G$ be a directed
graph on the vertices $0, \dots, n-1$, let $w(u, v)$ be a natural-number weight for every
ordered pair of vertices, and let $s$, $t$ and $p$ be vertices. If Dijkstra's algorithm on $G$
with weights $w$ from source $s$ outputs $p$ as the predecessor of $t$, then $G$ has an edge
from $p$ to $t$, the distances $d(p)$ and $d(t)$ output for $p$ and $t$ are both finite, and
$d(t) = d(p) + w(p, t)$.
