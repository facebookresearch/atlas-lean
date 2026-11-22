# Removing the minimum preserves AVL balance

Let $t$ be a binary tree with a cached height
at each node whose cached heights are correct, and which is balanced: at every node the cached
heights of the two subtrees differ by at most one. Then the tree obtained from $t$ by removing its
leftmost key, rebalancing on the way back up, is again balanced.
