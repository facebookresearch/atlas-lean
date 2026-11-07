# Search misses a key deleted from an order-statistic tree

Let $\alpha$ be a linearly ordered
type, $k \in \alpha$ and $T$ an ordered order-statistic tree over $\alpha$ (at every node, all keys
of the left subtree are smaller and all keys of the right subtree are larger than the node's
key). Comparison search for $k$ in the tree obtained by deleting $k$ from $T$ returns false.
