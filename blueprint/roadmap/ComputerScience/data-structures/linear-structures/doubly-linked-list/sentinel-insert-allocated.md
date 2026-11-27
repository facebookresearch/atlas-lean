# Sentinel insertion preserves allocation

Let $S$ be a store of $n$ cells, each empty or
holding a node, in which the cells $x$ and $y$ are allocated, the next pointer of $y$ is not NIL,
and the cell it points to is allocated. Let $S'$ be the store returned by sentinel insertion of
$x$ after $y$. Then every cell $z$ is allocated in $S'$ if and only if it is allocated in $S$.

No distinctness of $x$, $y$, $z$ and the successor of $y$ is assumed.
