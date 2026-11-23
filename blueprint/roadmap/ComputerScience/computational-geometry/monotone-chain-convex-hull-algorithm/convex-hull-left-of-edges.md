# The hull polygon contains every input point

Let $p_1, \dots, p_n$ be $n \ge 2$ points of
$\Bbbk^2$, for an ordered field $\Bbbk$, strictly increasing in the lexicographic order on $(x, y)$,
and let $v_1, \dots, v_m$ be the vertices of their convex hull computed by the monotone chain
algorithm. Then for every input point $s$ and every edge $(a, b)$ of the closed polygon
$v_1, \dots, v_m, v_1$ (that is, $a, b$ consecutive in this sequence), the cross product
$(b - a) \times (s - a)$ is nonnegative: $s$ lies on or to the left of the edge from $a$ to $b$.
