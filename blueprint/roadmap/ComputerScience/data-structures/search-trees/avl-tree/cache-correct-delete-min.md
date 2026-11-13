# Minimum deletion keeps cached heights correct

Let $t$ be a binary tree with a cached height
at each node whose cached heights are correct: each node stores one more than the larger of the
cached heights of its two subtrees, the empty tree having height $0$. Then the cached heights of
the tree obtained from $t$ by minimum deletion (removing its leftmost key, rebalancing on the way
back up) are again correct.
