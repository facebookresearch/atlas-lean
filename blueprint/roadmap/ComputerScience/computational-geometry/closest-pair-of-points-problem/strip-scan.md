# Closest-pair strip scan

Let $K$ be a linearly ordered field, $\delta \in K$ and
$c_1, \dots, c_n$ a list of points of $K^2$. For each $i$, the strip scan runs the strip scan from
$c_i$ with threshold $\delta$ on the later points $c_{i+1}, \dots, c_n$. It returns the least of
the values these scans return, or no value if none of them returns a value, and its cost is the
sum of their costs.
