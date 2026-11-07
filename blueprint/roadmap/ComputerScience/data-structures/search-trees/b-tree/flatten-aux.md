# Accumulating flattening of a B-tree

Given a raw B-tree $T$ and a list $s$, this returns
the inorder traversal of $T$ followed by $s$. For a leaf it is the leaf's key list followed by
$s$. For an internal node with separator keys $k_1, \dots, k_m$ and children $c_0, \dots, c_n$
it is the sequence $c_0, k_1, c_1, k_2, \dots$, in which children and keys alternate starting
with a child until one of the two lists runs out, then the remaining keys or children in
order, and finally $s$; each key contributes itself, and each child contributes its own
accumulating flattening with everything after it as the suffix. In particular every key of
the tree occurs in the result.

The result is built from right to left, so each key is copied only once.
