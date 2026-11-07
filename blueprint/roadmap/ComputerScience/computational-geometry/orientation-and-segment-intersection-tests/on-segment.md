# The ON-SEGMENT test

For points $p_i = (x_i, y_i)$, $p_j = (x_j, y_j)$ and
$p_k = (x_k, y_k)$ in $K^2$, where $K$ is a linearly ordered field, CLRS's
ON-SEGMENT$(p_i, p_j, p_k)$ is the Boolean that is true exactly when $p_k$ lies in the bounding box
of $p_i$ and $p_j$, that is, $\min(x_i, x_j) \le x_k \le \max(x_i, x_j)$ and
$\min(y_i, y_j) \le y_k \le \max(y_i, y_j)$.
