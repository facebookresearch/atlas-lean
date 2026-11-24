# Select in an order-statistic tree

For an order-statistic tree $T$ and a natural number
$i$, select at index $i$ in $T$ is computed by descending from the root. It returns nothing for
the empty tree. At a node with key $k$, left subtree $L$ and right subtree $R$, it is select at
index $i$ in $L$ if $i < s(L)$; it returns $k$ if $i = s(L)$; and it is select at index
$i - s(L) - 1$ in $R$ if $i > s(L)$. Here $s(L)$ is the subtree size cached at the root of $L$,
and $0$ if $L$ is empty.

When the cached sizes are correct, this returns the key at zero-based position $i$ of the
inorder traversal, and nothing if $T$ has at most $i$ nodes.
