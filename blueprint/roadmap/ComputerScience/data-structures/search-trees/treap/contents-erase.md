# Treap inorder contents after erasure

Let the keys come from a linearly ordered type, let
$t$ be a tree and $k$ a key, and let $L$ and $G$ be the lower and upper trees produced by
splitting $t$ at $k$. Then the inorder list of key-value pairs of the tree obtained by erasing
$k$ from $t$ is the inorder list of $L$ followed by the inorder list of $G$.
