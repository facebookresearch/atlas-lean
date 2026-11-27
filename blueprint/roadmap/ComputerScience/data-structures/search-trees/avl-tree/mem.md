# Membership in an AVL tree

A key $x$ belongs to a tree $T$ when $x$ belongs to the binary
tree obtained from $T$ by erasing the cached heights. Equivalently, no key belongs to the empty
tree, and $x$ belongs to a node with left subtree $L$, key $k$ and right subtree $R$ exactly when
$x$ belongs to $L$, $x = k$, or $x$ belongs to $R$.
