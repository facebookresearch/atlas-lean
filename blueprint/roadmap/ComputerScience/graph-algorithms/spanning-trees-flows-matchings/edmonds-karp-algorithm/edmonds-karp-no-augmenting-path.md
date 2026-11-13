# No augmenting path remains after Edmonds–Karp

Let $c$ be a capacity matrix with
natural-number entries on the vertices $\{0, \dots, n-1\}$ and let $s$ and $t$ be distinct
vertices. Then $t$ is not reachable from $s$ in the residual graph of the flow returned
by the Edmonds–Karp algorithm on $c$, $s$, $t$.
