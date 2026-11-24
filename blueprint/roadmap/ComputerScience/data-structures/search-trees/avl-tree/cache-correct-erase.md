# Deletion keeps cached heights correct

Let $t$ be a binary tree with keys from a linearly
ordered type and a cached height at each node whose cached heights are correct: each node stores
one more than the larger of the cached heights of its two subtrees, the empty tree having height
$0$. Then for every key $x$, the cached heights of the tree obtained from $t$ by deleting $x$,
rebalancing along the search path, are again correct.
