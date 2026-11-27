# AVL deletion preserves search-tree order

Let $T$ be a binary tree with cached heights over
a linearly ordered type, ordered as a search tree (every key in a left subtree is smaller, and
every key in a right subtree is larger, than the key at the node). Then for every key $x$, the
tree obtained by deleting $x$ from $T$ with rebalancing is again ordered as a search tree.
