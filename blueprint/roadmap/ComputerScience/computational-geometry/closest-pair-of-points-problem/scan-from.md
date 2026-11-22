# Strip scan from a point

Let $K$ be a linearly ordered field, and write
$d(p, q) = (p_1 - q_1)^2 + (p_2 - q_2)^2$ for the squared distance between points
$p = (p_1, p_2)$ and $q = (q_1, q_2)$ of $K^2$. Let $\delta \in K$, let $p = (p_1, p_2)$ be a
point of $K^2$ and $c_1, \dots, c_m$ a list of points $c_l = (x_l, y_l)$ of $K^2$, and let
$k \le m$ be largest such that $(y_l - p_2)^2 < \delta$ for all $1 \le l \le k$. The scan from $p$
with threshold $\delta$ returns no value if $k = 0$ and $\min_{1 \le l \le k} d(p, c_l)$
otherwise. It is charged one unit of cost per point $c_1, \dots, c_k$: it stops at the first
point whose squared vertical gap to $p$ is at least $\delta$, without computing its distance.
