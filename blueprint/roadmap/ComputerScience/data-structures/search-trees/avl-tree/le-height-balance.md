# Rebalancing does not drop below the taller child

Write $h(T)$ for the cached height at the
root of a tree $T$, with $h$ of the empty tree equal to $0$, and write $\mathrm{balance}(L, k, R)$
for the AVL rebalancing of the node with left subtree $L$, key $k$ and right subtree $R$. If $L$
and $R$ are trees whose cached heights are correct at every node, then for every key $k$ we have
$\max(h(L), h(R)) \le h(\mathrm{balance}(L, k, R))$.
