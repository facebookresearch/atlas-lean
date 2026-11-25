# Counted AVL node rebuild

Write $h(t)$ for the height cached at the root of a binary tree $t$ with cached heights ($0$ for the empty tree). For trees $L$, $R$ with cached heights and a key $k$, the counted node rebuild returns the node with left subtree $L$, key $k$, right subtree $R$ and cached height $\max(h(L), h(R)) + 1$, together with a cost of exactly $1$.

Discarding the cost gives the ordinary smart constructor on the same two subtrees and key.
