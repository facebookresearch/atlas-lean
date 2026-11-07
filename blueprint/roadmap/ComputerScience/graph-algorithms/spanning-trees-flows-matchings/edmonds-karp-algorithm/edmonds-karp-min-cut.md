# The Edmonds–Karp flow value equals its residual cut capacity

Let $c$ be a capacity
matrix with natural-number entries on the vertices $\{0, \dots, n-1\}$, let $s$ and $t$ be
distinct vertices, and let $f$ be the flow returned by the Edmonds–Karp algorithm on $c$,
$s$, $t$. Then the net flow of $f$ out of $s$ equals the capacity of the cut formed by the
vertices reachable from $s$ in the residual graph of $f$.
