# Rebalancing an interval-tree node with exact stored height restores AVL balance

Let $L$
and $R$ be interval trees that are AVL balanced with exact stored heights, with heights $h_L$ and
$h_R$ satisfying $h_L \le h_R + 2$ and $h_R \le h_L + 2$. Let $N$ be a node with left subtree $L$,
entry $e$ and right subtree $R$ whose stored height is $\max(h_L, h_R) + 1$ (its stored size and
stored maximum are arbitrary), and let $B$ be the tree obtained by rebalancing $N$ (the tree
component of the result; the cost is ignored). Then $B$ is AVL balanced with exact stored heights,
the height of $B$ is $\max(h_L, h_R) + 1$ or $\max(h_L, h_R)$, and it is $\max(h_L, h_R)$ only if
$h_L = h_R + 2$ or $h_R = h_L + 2$.
