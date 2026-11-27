# Rebalancing when the heights of the children differ by at most one

Let $l$ and $r$ be
trees with cached heights, let $x$ be a key, and write $h(T)$ for the cached height at the root
of a tree $T$ (zero for the empty tree). If $h(l) \le h(r) + 1$ and $h(r) \le h(l) + 1$, then
$\mathrm{balance}(l, x, r)$ is the node with left subtree $l$, key $x$, right subtree $r$ and
cached height $\max(h(l), h(r)) + 1$; no rotation is performed.
