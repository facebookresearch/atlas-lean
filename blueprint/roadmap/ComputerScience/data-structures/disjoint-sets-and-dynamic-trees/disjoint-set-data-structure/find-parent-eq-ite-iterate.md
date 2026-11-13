# FIND compresses exactly the original path to the root

Let $S$ be a union-find structure
with parent map $p$ (where $p(i) = i$ for $i \ge |S|$), let $x < |S|$, and let $p'$ be the parent
map of the structure produced by FIND with path compression on $x$. Then for every natural number
$i$, $p'(i)$ is the root of $x$ if $i = p^k(x)$ for some $k \ge 0$, and $p'(i) = p(i)$
otherwise.
