# Decrease-key at an unresolved address does nothing

Let $H$ be a Fibonacci heap, $i$ a
root index and $p$ a path of child indices. If cutting the subtree at path $p$ out of the $i$-th
tree of the root list of $H$ fails, then for every key $k$, decreasing the key at root index $i$
and path $p$ to $k$ returns $H$ unchanged.
