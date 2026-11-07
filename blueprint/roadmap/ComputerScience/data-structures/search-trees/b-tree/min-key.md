# Leftmost key of a B-tree

For a tree $T$, the leftmost key of $T$ is an optional key
defined by descending the leftmost spine: for a leaf it is the first of its keys (none if the
leaf has no keys); for an internal node with at least one child it is the leftmost key of its
first child; for an internal node with no children it is the first of its separator keys (none
if there are none).

If $T$ satisfies the structural B-tree invariant for a minimum degree $t \ge 2$ and has at least
one key at its root, the leftmost key exists and is the first key of the inorder flattening of
$T$, so on an ordered tree it is the least key.
