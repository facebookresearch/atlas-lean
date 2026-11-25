# Weight form of the balance condition at a node

Write $|t|$ for the number of keys of
a tree $t$ and $w(t) = |t| + 1$ for its weight. Let $N$ be the node with key $k$, left subtree
$L$ and right subtree $R$. Then $N$ is weight-balanced if and only if $L$ and $R$ are
weight-balanced, $4\,w(L) \le 3\,w(N)$ and $4\,w(R) \le 3\,w(N)$. This is the classical
$\mathrm{BB}[1/4]$ invariant: each child has weight at most three quarters of the weight of
the node.
