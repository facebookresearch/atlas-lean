# Rank after deletion in an order-statistic tree

Let $\alpha$ be a linearly ordered type
and let $T$ be an order-statistic tree over $\alpha$ that is ordered and whose cached subtree
sizes are correct. Let $k$ and $q$ be keys and let $T'$ be the tree obtained from $T$ by
deleting $k$. Then the rank of $q$ in $T'$, computed by navigation with cached sizes, equals the
number of entries strictly smaller than $q$ in the inorder traversal of $T'$ with its cached
sizes removed.
