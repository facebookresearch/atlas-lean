# Decrease-key with a larger key does nothing

Let $H$ be a Fibonacci heap, $i$ a root index,
$p$ a path of child indices and $k$ a key. Suppose that cutting the subtree at path $p$ out of
the $i$-th tree of the root list of $H$ succeeds and extracts the subtree $S$, and that $k$ is
not at most the root of $S$ (keys are linearly ordered, so $k$ is greater than that root). Then
decreasing the key at root index $i$ and path $p$ to $k$ returns $H$ unchanged.
