# Characterization of a successful linear search

For every predicate $p$ on a type
$\alpha$, every list $L = (x_0, \dots, x_{n-1})$ over $\alpha$ and every natural number $i$,
linear search for $p$ on $L$ returns the index $i$ if and only if $i < n$, $p(x_i)$ is true, and
$p(x_j)$ is false for every $j < i$.
