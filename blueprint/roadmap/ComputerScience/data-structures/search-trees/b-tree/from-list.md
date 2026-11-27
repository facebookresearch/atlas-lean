# B-tree built from a list

For a linearly ordered key type and a natural number $t$, the
tree built from the empty list is the empty tree, and the tree built from a list with head $x$
and tail $L$ is the result of inserting $x$, with minimum degree $t$, into the tree built from
$L$. Thus the elements are inserted from right to left.
