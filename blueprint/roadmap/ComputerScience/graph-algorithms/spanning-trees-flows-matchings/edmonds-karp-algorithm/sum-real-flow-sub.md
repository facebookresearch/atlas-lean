# Net outflow in the arc representation

Let $f$ be a skew-symmetric integer flow matrix on
the vertices $0, \dots, n-1$, so $f(u, v) = -f(v, u)$ for all $u, v$, and let
$a(u, v) = \max(f(u, v), 0)$ be its arc flow, viewed as real numbers. Then for every vertex $v$,
$\sum_w a(v, w) - \sum_u a(u, v) = \sum_w f(v, w)$, the net flow leaving $v$.
