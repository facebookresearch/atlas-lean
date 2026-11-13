# Inorder flattening of a B-tree

The flattening of a raw B-tree is the list of its keys
defined recursively: for a leaf it is the leaf's key list, and for an internal node with keys
$k_1, k_2, \dots$ and children $c_1, c_2, \dots$ it is the flattening of $c_1$, then $k_1$, then
the flattening of $c_2$, then $k_2$, and so on, alternating while both lists last; whatever
remains of the longer list is then appended in order, each surplus child contributing its
flattening and each surplus key contributing itself. In particular every key of the tree occurs
in the flattening.

The flattening is computed in linear time by an accumulator-passing auxiliary function.
