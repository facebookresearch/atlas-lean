# After access, the accessed vertex ends its preferred path

Let $s$ be a valid link-cut
tree state and let $x$ be a vertex of its represented forest. Then, after accessing $x$, the
preferred-path decomposition of the new state contains a path $p$ whose last vertex is $x$, and
$p$ is the path from the root down to $x$ in some tree of the represented forest of $s$.

Paths are listed from the root downward, so $x$ is the deepest vertex of $p$. No auxiliary splay
tree is modeled, so this is only the endpoint property of the accessed preferred path.
