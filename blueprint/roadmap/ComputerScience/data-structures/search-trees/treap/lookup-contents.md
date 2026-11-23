# Treap lookup agrees with the inorder contents

Let $t$ be a tree with keys in a linearly
ordered type that is ordered as a binary search tree (every key in a left subtree is smaller and
every key in a right subtree is larger than the node's key). For every key $k$ and value $v$,
looking up $k$ in $t$ returns $v$ if and only if the pair $(k, v)$ occurs in the inorder
key-value list of $t$.
