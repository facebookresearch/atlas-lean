# Valid AVL tree

Let $\alpha$ be a type with a relation $<$. A binary tree with cached heights over $\alpha$ is a valid AVL tree when it is ordered (the binary tree obtained by erasing the cached heights is a binary search tree for $<$: at every node each key of the left subtree is less than the node's key and the node's key is less than each key of the right subtree), has correct cached heights (every node stores one more than the larger cached height of its two subtrees, the empty tree having height $0$), and is balanced (at every node the cached heights of the two subtrees differ by at most one). Together, correct caches and the balance condition on cached heights say that at every node the true heights of the two subtrees differ by at most one.

The empty tree satisfies all three conditions for any relation $<$.
