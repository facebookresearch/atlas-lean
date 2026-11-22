# Keys left after removing the minimum exceed it

Let $t$ be a binary tree with keys from a
linearly ordered type and a cached height at each node, and suppose $t$ is ordered: at every node,
all keys in the left subtree are strictly smaller and all keys in the right subtree are strictly
larger than the key at that node. Let $m$ be the leftmost key of $t$, or an arbitrary default
value if $t$ is empty. Then every key of the tree obtained from $t$ by removing its leftmost key,
rebalancing on the way back up, is strictly greater than $m$.
