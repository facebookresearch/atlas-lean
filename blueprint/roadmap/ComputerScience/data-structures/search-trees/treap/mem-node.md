# Entry membership in a treap tree

A key $k$, value $v$ and priority $p$ form an entry
of a treap tree when some node stores exactly $k$, $v$ and $p$: the empty tree has no
entries, and $(k, v, p)$ is an entry of a node with left subtree $L$, root key $r$, root value
$w$, root priority $q$ and right subtree $R$ exactly when it is an entry of $L$, or $k = r$,
$v = w$ and $p = q$, or it is an entry of $R$.
