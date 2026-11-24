# Two-sided capacity bounds for a feasible flow

Let $c$ be a capacity matrix with
natural-number entries on the vertices $\{0, \dots, n-1\}$, let $s$ and $t$ be vertices,
and let $f$ be a flow that is feasible for $c$, $s$, $t$. Then for all vertices $u$ and
$v$, we have $-c(v, u) \le f(u, v) \le c(u, v)$.

The lower bound follows from skew symmetry and the upper bound on the reverse entry.
