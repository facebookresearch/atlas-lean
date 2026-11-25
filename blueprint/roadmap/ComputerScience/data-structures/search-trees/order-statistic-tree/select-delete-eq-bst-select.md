# Selection after deletion in an order-statistic tree

Let $\alpha$ be a linearly ordered
type and let $T$ be an order-statistic tree over $\alpha$ whose cached subtree sizes are correct.
Let $k$ be a key and let $T'$ be the tree obtained from $T$ by deleting $k$. Then for every
natural number $i$, selecting position $i$ in $T'$ by navigation with cached sizes returns the
entry at zero-based position $i$ of the inorder traversal of $T'$ with its cached sizes removed,
and returns nothing when that traversal has at most $i$ entries.
