# Root list after decrease-key

Let $H$ be a Fibonacci heap, $i$ a root index, $p$ a path of
child indices and $k$ a key. Suppose that cutting the subtree at path $p$ out of the $i$-th tree
of the root list of $H$ succeeds, extracting the subtree $S$ and leaving the forest $R$, and that
$k$ is at most the root of $S$. Then the root list of the heap obtained from $H$ by decreasing
the key at root index $i$ and path $p$ to $k$ consists of $S$ with its root replaced by $k$,
followed by the trees of $R$ in order.
