# Number of keys of an AVL tree

For a binary tree with cached heights (each node stores a natural number, its cached height, besides its left subtree, key and right subtree), the size of $t$ is the number of nodes of the binary tree obtained from $t$ by erasing its cached heights, that is, the number of nodes (keys) of $t$. The cached height values play no role.

The empty tree has size $0$. A node with left and right subtrees $L$ and $R$ has size $|L|+|R|+1$, regardless of the cached height. This includes a node constructed with its correct cached height.
