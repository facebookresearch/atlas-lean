# Least squared distance from a point to a list

Let $K$ be a linearly ordered field, and
write $d(p, q) = (p_1 - q_1)^2 + (p_2 - q_2)^2$ for the squared distance between points
$p = (p_1, p_2)$ and $q = (q_1, q_2)$ of $K^2$. For a point $p$ and a list $c_1, \dots, c_m$ of
points of $K^2$, the least squared distance from $p$ to the list is no value if $m = 0$ and
$\min_{1 \le k \le m} d(p, c_k)$ otherwise. Computing it is charged one unit of cost per point of
the list, $m$ units in total.
