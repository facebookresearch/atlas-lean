# Counted AVL deletion returns the deleted tree

For a linearly ordered key type, every key $x$ and every binary tree $t$ with cached heights, the tree returned by counted deletion of $x$ from $t$ equals the AVL deletion of $x$ from $t$, including the case of a node with two children, which is replaced using the leftmost key of its right subtree and that subtree with its leftmost key removed.
