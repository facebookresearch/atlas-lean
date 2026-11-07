# Rightmost key of a B-tree

For a tree $T$, the rightmost key of $T$ is an optional key
defined by descending the rightmost spine: for a leaf it is the last of its keys (none if the
leaf has no keys); for an internal node with at least one child it is the rightmost key of its
last child; for an internal node with no children it is the last of its separator keys (none
if there are none).

If $T$ satisfies the structural B-tree invariant for a minimum degree $t \ge 2$ and has at least
one key at its root, the rightmost key exists and is the last key of the inorder flattening of
$T$, so on an ordered tree it is the greatest key. Each step splits a child list of length at
most $2t$, so on a valid tree of height $h$ the descent costs $O(t h)$, without computing the
flattening.
