# Deletion from a B-tree erases the key from its flattening

Let $t \ge 2$ and let $T$ be a
B-tree of minimum degree $t$ over a linearly ordered key type. For every key $x$, the inorder
flattening of the tree obtained from $T$ by top-down deletion of $x$ with minimum degree $t$ is
the flattening of $T$ with the first occurrence of $x$ removed (unchanged if $x$ does not occur).
