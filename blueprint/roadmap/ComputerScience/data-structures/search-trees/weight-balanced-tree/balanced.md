# Weight-balanced trees

Write $|t|$ for the number of keys of a binary tree $t$ and
$w(t) = |t| + 1$ for its weight. A binary tree is weight-balanced, or satisfies the
invariant $\mathrm{BB}[1/4]$, when it is empty, or when it is a node with left subtree $L$
and right subtree $R$ such that $L$ and $R$ are weight-balanced,
$4\,w(L) \le 3(w(L) + w(R))$ and $4\,w(R) \le 3(w(L) + w(R))$. Since the weight of a node
is $w(L) + w(R)$, this says that each child has weight at most three quarters of the
weight of the node.
