# Ordered AVL trees

Let $\alpha$ be a type with a relation $<$. A tree with cached
heights over $\alpha$ is ordered when the binary tree obtained by erasing its cached heights
is an ordered binary search tree: the empty tree is ordered, and a node with key $k$ is
ordered when its left and right subtrees are ordered, every key of the left subtree is less
than $k$, and every key of the right subtree is greater than $k$.
