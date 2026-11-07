# AVL balance invariant

The empty tree is balanced. A node with left subtree $\ell$ and
right subtree $r$ is balanced when $\ell$ and $r$ are balanced and $h(\ell) \le h(r) + 1$ and
$h(r) \le h(\ell) + 1$, where $h$ denotes the height cached at the root of a tree (and $0$ for the
empty tree). Equivalently, at every node the balance factor $h(\ell) - h(r)$ lies in
$\{-1, 0, 1\}$.
