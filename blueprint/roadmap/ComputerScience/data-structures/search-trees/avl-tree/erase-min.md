# Removing the leftmost key of an AVL tree

For a tree $t$ with cached heights, the tree
obtained by removing the leftmost key of $t$ is defined by recursion on $t$. The empty tree stays
empty. A node whose left subtree is empty is replaced by its right subtree. A node with nonempty
left subtree $l$, key $k$ and right subtree $r$ is replaced by $\mathrm{balance}(l', k, r)$, where
$l'$ is $l$ with its leftmost key removed and $\mathrm{balance}$ is the AVL rebalancing function.
