# Collinear-endpoint step of SEGMENTS-INTERSECT

Let $K$ be a linearly ordered field,
$d \in K$ and $p_i, p_j, p_k \in K^2$. When $d = 0$, this step costs one unit and returns the value
of ON-SEGMENT$(p_i, p_j, p_k)$; when $d \neq 0$, it costs nothing and returns false.

In SEGMENTS-INTERSECT, $d$ is the direction of $p_k$ relative to $p_i$ and $p_j$.
