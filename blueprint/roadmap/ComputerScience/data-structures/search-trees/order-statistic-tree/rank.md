# Rank in an order-statistic tree

For a key $q$ of a linearly ordered type, the rank of
$q$ in an order-statistic tree is computed by descending from the root. It is $0$ for the empty
tree. At a node with key $k$, left subtree $L$ and right subtree $R$, it is the rank of $q$ in
$L$ if $q < k$; it is $s(L) + 1$ plus the rank of $q$ in $R$ if $k < q$; and it is $s(L)$ if
$q = k$. Here $s(L)$ is the subtree size cached at the root of $L$, and $0$ if $L$ is empty.

When the cached sizes are correct and the tree is ordered, this is the number of keys in the
tree strictly smaller than $q$.
