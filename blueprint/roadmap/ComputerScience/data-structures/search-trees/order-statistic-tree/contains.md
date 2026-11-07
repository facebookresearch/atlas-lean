# Search in an order-statistic tree

Let $\alpha$ be a linearly ordered type and
$q \in \alpha$. Searching for $q$ in the empty tree returns false. At a node with key $k$, the
search continues in the left subtree if $q < k$, continues in the right subtree if $k < q$, and
returns true otherwise.
