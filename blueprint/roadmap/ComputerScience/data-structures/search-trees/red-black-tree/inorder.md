# Inorder traversal of a red-black tree

The inorder traversal of a red-black tree $t$ is
the binary-search-tree inorder traversal of the color erasure of $t$, computed in linear time
with an accumulator starting from the empty list. It lists the keys of $t$ from left to right:
the empty tree gives the empty list, and a node with key $k$ and subtrees $l$ and $r$ gives the
traversal of $l$, then $k$, then the traversal of $r$.
