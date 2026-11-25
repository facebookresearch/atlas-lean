# Effect of path-compressing find on each node

Let $s$ be a union-find structure on the
indices $0, \dots, n-1$ with parent function $p$, let $x < n$, and let $r$ be the root of $x$ in
$s$. After find with path compression is run on $x$, for every index $i < n$ the node at $i$ in
the resulting array keeps its rank from $s$, and its parent is $r$ if $i = p^k(x)$ for some
$k \ge 0$, and is its original parent $p(i)$ otherwise.
