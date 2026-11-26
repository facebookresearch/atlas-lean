# Height-indexed B-tree deletion

Given a height $h$, a minimum degree $t$, a key $x$ of a
linearly ordered key type and a tree $T$, the result is defined as follows. If $T$ is a leaf, the
result is the leaf whose key list is that of $T$ with the first occurrence of $x$ erased,
whatever $h$ is. If $T$ is an internal node and $h = 0$, the result is $T$. If $T$ is an internal
node and $h = n + 1$, the result is the internal node whose separator and child lists are
obtained by deletion of $x$ within the node of $T$ (with minimum degree $t$), where deletion from
a child is height-indexed deletion with minimum degree $t$ at height $n$.

The correctness specification only covers heights that match the shape of the tree.
