# Decrease-key preserves the number of elements

Let $H$ be a Fibonacci heap, $i$ a root
index, $p$ a path of child indices and $k$ a key. Suppose that cutting the subtree at path $p$
out of the $i$-th tree of the root list of $H$ succeeds and extracts the subtree $S$, and that
$k$ is at most the root of $S$. Then the multiset represented by the heap obtained from $H$ by
decreasing the key at root index $i$ and path $p$ to $k$ has the same number of elements,
counted with multiplicity, as the multiset represented by $H$.
