# Deletion preserves order in an order-statistic tree

Let $\alpha$ be a linearly ordered
type and let $T$ be an order-statistic tree over $\alpha$ that is ordered, that is, after its
cached sizes are removed, every key in a left subtree is strictly smaller than the key of its node
and every key in a right subtree is strictly larger. Then for every key $k$, the tree obtained
from $T$ by deleting $k$ is again ordered.
