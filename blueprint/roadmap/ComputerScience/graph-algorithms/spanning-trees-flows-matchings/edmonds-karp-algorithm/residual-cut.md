# Residual cut

Let $c$ be a capacity matrix assigning a natural number $c(u, v)$ to each
ordered pair of vertices among $0, \dots, n - 1$, let $f$ be a flow on these vertices, and let $s$
be a vertex. The residual cut of $c$, $f$ and $s$ is the set of vertices visited by breadth-first
search from $s$ in the residual graph of $c$ and $f$, that is, the set of vertices reachable from
$s$ in that residual graph.
