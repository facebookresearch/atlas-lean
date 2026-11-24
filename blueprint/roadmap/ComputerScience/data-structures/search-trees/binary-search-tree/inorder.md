# Inorder traversal of a binary tree

The inorder traversal of a binary tree $t$ is the
accumulated inorder traversal of $t$ onto the empty list. Equivalently, the empty tree gives the
empty list, and a node with key $k$, left subtree $L$ and right subtree $R$ gives the inorder
traversal of $L$, then $k$, then the inorder traversal of $R$.
