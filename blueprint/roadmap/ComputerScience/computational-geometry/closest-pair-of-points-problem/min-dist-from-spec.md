# The nearest-point scan returns the least squared distance

Let $K$ be a linearly ordered
field, write $d(u, v) = (x - x')^2 + (y - y')^2$ for the squared distance between points
$u = (x, y)$ and $v = (x', y')$ of $K^2$, let $p \in K^2$, and let $qs$ be a list of points in
$K^2$. If the scan for the least squared distance from $p$ to the entries of $qs$ returns a value
$\delta$, then $\delta = d(p, q)$ for some entry $q$ of $qs$. For every entry $q$ of $qs$, the
scan returns a value $\delta$ with $\delta \le d(p, q)$.
