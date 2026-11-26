# AVL rebalancing yields a balanced tree

Let $l$ and $r$ be trees whose cached heights are
correct at every node and which are balanced (at every node the cached heights of the two
subtrees differ by at most one), let $x$ be a key, and write $h(T)$ for the cached height at the
root of a tree $T$ (zero for the empty tree). If $h(l) \le h(r) + 2$ and $h(r) \le h(l) + 2$,
then $\mathrm{balance}(l, x, r)$ is balanced.

One insertion step maintains this precondition.
