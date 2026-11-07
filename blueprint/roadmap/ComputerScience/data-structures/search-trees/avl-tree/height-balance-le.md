# Upper bound on height after AVL rebalancing

Let $l$ and $r$ be trees whose cached
heights are correct at every node, and write $h$ for the cached height. Then for every key $k$,
the rebalanced node $b$ built from $l$, $k$ and $r$ satisfies $h(b) \le \max(h(l), h(r)) + 1$.
