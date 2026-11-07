# Linear search returns the first satisfying index

For every predicate $p$ on a type
$\alpha$ and every list $L = (x_0, \dots, x_{n-1})$ over $\alpha$, the index returned by linear
search for $p$ on $L$ (ignoring its cost) equals the result of the standard library's
first-index search: the least $i < n$ with $p(x_i)$ true, or no index if $p(x_i)$ is false for
every $i < n$.
