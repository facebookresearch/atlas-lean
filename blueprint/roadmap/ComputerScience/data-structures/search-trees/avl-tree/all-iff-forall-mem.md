# The all-keys predicate in terms of membership (AVL trees)

For a predicate $p$ on keys and
a tree $t$ with cached heights, $\mathrm{All}(p, t)$ holds if and only if $p(x)$ holds for every
$x \in t$, where $x \in t$ means that $x$ is the key of some node of $t$.
