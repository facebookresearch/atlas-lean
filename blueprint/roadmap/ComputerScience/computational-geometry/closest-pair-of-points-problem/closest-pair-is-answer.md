# The closest-pair algorithm returns the answer

Let $K$ be a linearly ordered field, write
$d(p, q) = (x - x')^2 + (y - y')^2$ for the squared distance between points $p = (x, y)$ and
$q = (x', y')$ of $K^2$, and let $ps$ be a list of points in $K^2$. If the divide-and-conquer
closest-pair algorithm returns a value $\delta$ on $ps$, then $\delta = d(p, q)$ for some entries
$p$, $q$ of $ps$ at different positions. For any two entries $p$, $q$ of $ps$ at different
positions, the algorithm returns a value $\delta$ with $\delta \le d(p, q)$.
