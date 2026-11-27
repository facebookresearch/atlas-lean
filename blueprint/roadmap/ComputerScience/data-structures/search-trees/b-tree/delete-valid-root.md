# Top-down deletion lowers the height by at most one

Let $t \ge 2$ and let $T$ be an
ordered tree over a linearly ordered key type (its inorder flattening is strictly increasing)
that satisfies the root invariant of B-trees of minimum degree $t$ at height $h$. For every key
$x$, the tree obtained by deleting $x$ from $T$ with minimum degree $t$ satisfies the root
invariant of minimum degree $t$ at height $h$ or at height $h - 1$, where $h - 1$ is truncated
subtraction, so equal to $0$ when $h = 0$.
