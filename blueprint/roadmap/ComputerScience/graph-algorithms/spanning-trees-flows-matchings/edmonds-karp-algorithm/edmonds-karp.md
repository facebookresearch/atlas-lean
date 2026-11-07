# Edmonds–Karp maximum flow

Let $c$ be a capacity function assigning a natural number
$c(u, v)$ to each ordered pair of vertices, and let $s$ and $t$ be vertices. If $s = t$, the
Edmonds–Karp flow is the zero flow. Otherwise it is the result of running at most $C + 1$ rounds
of bottleneck augmentation from the zero flow, where $C = \sum_v c(s, v)$ is the total capacity
leaving $s$: each round looks for a shortest path from $s$ to $t$ in the residual graph, stops if
there is none, and otherwise augments the flow along that path by its bottleneck.
