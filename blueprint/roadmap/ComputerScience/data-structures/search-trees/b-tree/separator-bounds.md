# Separator bounds in an ordered B-tree node

Let $K_1$ and $K_2$ be lists of keys,
$k$ a key, and $C_1$ and $C_2$ lists of B-trees such that $C_1$ has exactly one more tree
than $K_1$ has keys. If the internal node whose key list is $K_1$ followed by $k$ followed
by $K_2$, and whose child list is $C_1$ followed by $C_2$, is ordered, then every key in the
flattening of the node with keys $K_1$ and children $C_1$ is less than $k$, and $k$ is less
than every key in the flattening of the node with keys $K_2$ and children $C_2$.

Here the last tree of $C_1$ is the subtree immediately left of $k$ and the first tree of
$C_2$ the one immediately right of it; in particular, every key in a child of an ordered
node lies strictly between the separators adjacent to it.
