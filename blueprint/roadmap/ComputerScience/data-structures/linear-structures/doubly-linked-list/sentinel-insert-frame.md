# Sentinel insertion leaves other cells unchanged

Let $S$ be a store of $n$ cells, each
empty or holding a node, in which the cells $x$ and $y$ are allocated, the next pointer of $y$ is
not NIL, and the cell it points to is allocated. Let $S'$ be the store returned by sentinel
insertion of $x$ after $y$. If a cell $z$ differs from $x$ and from $y$, and the next pointer of
$y$ in $S$ is not $z$, then $z$ has the same content in $S'$ as in $S$.
