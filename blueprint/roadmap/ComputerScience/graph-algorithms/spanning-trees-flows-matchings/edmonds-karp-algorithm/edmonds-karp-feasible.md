# The Edmonds–Karp flow is feasible

For every capacity matrix $c$ with
natural-number entries on the vertices $\{0, \dots, n-1\}$ and all vertices $s$ and $t$,
the flow $f$ returned by the Edmonds–Karp algorithm on $c$, $s$, $t$ is feasible for $c$,
$s$, $t$: it is skew-symmetric, satisfies $f(u, v) \le c(u, v)$ for all vertices $u, v$,
and has zero net outflow at every vertex other than $s$ and $t$.
