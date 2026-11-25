# Node construction preserves interval validity

If $L$ and $R$ are interval trees
satisfying the validity invariant and $e$ is an entry whose interval $[a, b]$ satisfies
$a \le b$, then the node with left subtree $L$, entry $e$ and right subtree $R$, built by the
node constructor that recomputes the cached fields, satisfies the validity invariant.
