# Rebalancing an AVL node preserves the search-tree order

Let $\alpha$ be a linearly
ordered type, let $k \in \alpha$, and let $L$ and $R$ be ordered trees with cached heights
over $\alpha$ such that every key of $L$ is less than $k$ and every key of $R$ is greater
than $k$. Then the tree that rebalancing produces from left subtree $L$, key $k$ and right
subtree $R$ is ordered.
