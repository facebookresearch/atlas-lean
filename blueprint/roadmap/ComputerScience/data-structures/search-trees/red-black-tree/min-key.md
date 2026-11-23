# Leftmost key of a red-black tree

For a red-black tree $t$ over a type $\alpha$, the
leftmost key of $t$ is either a key in $\alpha$ or undefined. It is undefined when $t$ is empty.
When $t$ is a node, of either color, with left subtree $l$ and key $k$, it is the leftmost key of
$l$ if that is defined, and $k$ otherwise. Hence the leftmost key is defined exactly when $t$ is
nonempty.

Under the search-tree invariant the leftmost key is the minimum key of the tree.
