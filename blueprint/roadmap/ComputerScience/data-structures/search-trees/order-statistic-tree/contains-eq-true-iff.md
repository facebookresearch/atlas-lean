# Search in an ordered order-statistic tree is correct

Let $\alpha$ be a linearly ordered
type and $T$ an order-statistic tree over $\alpha$ that is ordered: after forgetting the cached
sizes, at every node all keys in the left subtree are smaller than the node's key and all keys in
the right subtree are larger. Then for every $q \in \alpha$, comparison search for $q$ in $T$
returns true if and only if $q$ is the key of some node of $T$.
