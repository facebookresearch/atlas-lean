# Order-statistic tree node with computed cache

Given a key $k$ and order-statistic
trees $L$ and $R$, the node built from them has key $k$, left subtree $L$, right subtree $R$,
and cached subtree size equal to the cached root size of $L$ plus the cached root size of $R$
plus one, where the empty tree has cached root size zero.
