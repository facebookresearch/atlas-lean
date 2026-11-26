# Ordered red-black tree

Let $\alpha$ be a type with a relation $<$. A red-black tree with
keys in $\alpha$ is ordered when, at every node with key $k$, every key $y$ in the left subtree
satisfies $y < k$ and every key $z$ in the right subtree satisfies $k < z$.

Equivalently, the binary tree obtained by erasing the colors is an ordered binary search tree.
