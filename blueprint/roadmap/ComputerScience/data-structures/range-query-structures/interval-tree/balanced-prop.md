# AVL balance of an interval tree

An interval tree is AVL balanced with exact stored heights
when it is empty, or when it is a node such that, writing $h_L$ and $h_R$ for the stored heights
of its left and right subtrees (the empty tree has height $0$), the node's stored height equals
$\max(h_L, h_R) + 1$, $h_L \le h_R + 1$, $h_R \le h_L + 1$, and both subtrees are again AVL
balanced with exact stored heights.
