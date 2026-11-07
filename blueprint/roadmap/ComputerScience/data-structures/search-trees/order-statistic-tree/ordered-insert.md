# Insertion preserves ordering of order-statistic trees

Let $T$ be an order-statistic
tree over a linearly ordered key type that is ordered, meaning that after its cached sizes are
erased, at every node each key of the left subtree is strictly smaller than the node's key and
each key of the right subtree is strictly larger. Then for every key $k$, the tree obtained by
inserting $k$ into $T$ is again ordered.
