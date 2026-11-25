# Minimum after decrease-key

Let $H$ be a Fibonacci heap whose minimum, as returned by
find-min, is $m$, and let $i$ be a root index, $p$ a path of child indices and $k$ a key. Suppose
that cutting the subtree at path $p$ out of the $i$-th tree of the root list of $H$ succeeds and
extracts the subtree $S$, and that $k$ is at most the root of $S$. Then find-min on the heap
obtained from $H$ by decreasing the key at root index $i$ and path $p$ to $k$ returns
$\min(k, m)$.
