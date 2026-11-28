# Merge

Skew-heap merge: keep the smaller root, merge the other tree
against that root's right child, and swap the children at every node
on the merge path. The recursive-equation counter `T_merge` follows
these same branches.
