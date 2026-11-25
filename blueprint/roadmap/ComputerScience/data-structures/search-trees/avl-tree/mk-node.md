# AVL node with computed height

Write $h(T)$ for the cached height at the root of a tree
$T$, with $h$ of the empty tree equal to $0$. Given trees $L$ and $R$ and a key $k$, this is the
node with left subtree $L$, key $k$ and right subtree $R$ whose cached height is
$\max(h(L), h(R)) + 1$.
