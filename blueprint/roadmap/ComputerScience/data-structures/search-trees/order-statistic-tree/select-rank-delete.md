# Selecting the rank of a surviving key after deletion

Let $\alpha$ be a linearly ordered
type, let $T$ be an order-statistic tree over $\alpha$ that is ordered and whose cached subtree
sizes are correct, let $k$ be a key, and let $T'$ be the tree obtained from $T$ by deleting $k$.
If $y$ is a key of $T'$, then selecting, with cached sizes, the position in $T'$ given by the
cached rank of $y$ in $T'$ returns $y$.
