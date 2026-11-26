# Brute-force closest pair

Let $K$ be a field with a linear order, and write
$d(p, q) = (x - x')^2 + (y - y')^2$ for the squared distance between points $p = (x, y)$ and
$q = (x', y')$ of $K^2$. On a list $c_1, \dots, c_n$ of points in $K^2$, the brute-force scan
returns no value if $n < 2$, and otherwise returns $\min_{i < j} d(c_i, c_j)$: for each $i$ it
computes the least squared distance from $c_i$ to the later points $c_{i+1}, \dots, c_n$, and
takes the least of these minima. It is charged one unit of cost per squared distance computed.
