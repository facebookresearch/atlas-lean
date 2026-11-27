# Boolean AVL balance check for interval trees

The balance check returns true on the empty
tree. On a node whose left and right subtrees have stored heights $h_L$ and $h_R$ (the empty tree
has height $0$), it returns true exactly when the node's stored height equals
$\max(h_L, h_R) + 1$, $h_L \le h_R + 1$, $h_R \le h_L + 1$, and the check returns true on both
subtrees.
