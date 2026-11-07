# Deleting a key preserves AVL balance

Let $t$ be a binary tree with keys from a linearly
ordered type and a cached height at each node, whose cached heights are correct, and which is
balanced: at every node the cached heights of the two subtrees differ by at most one. Then for
every key $x$, the tree obtained from $t$ by deleting $x$, rebalancing along the search path, is
again balanced.
