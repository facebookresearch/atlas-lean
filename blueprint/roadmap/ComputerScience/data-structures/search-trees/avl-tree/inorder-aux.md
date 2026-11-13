# Inorder traversal of an AVL tree onto a suffix

Given a tree $t$ and a list $s$, this is
the list of keys of $t$ in inorder (left subtree, root key, right subtree, recursively)
followed by $s$. It is computed in linear time by the binary search tree traversal of $t$ with
its cached heights erased.
