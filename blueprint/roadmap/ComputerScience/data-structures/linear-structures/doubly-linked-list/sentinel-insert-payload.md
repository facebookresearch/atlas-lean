# Sentinel insertion preserves payloads

Let $S$ be a store of $n$ cells, each empty or
holding a node, in which the cells $x$ and $y$ are allocated, the next pointer of $y$ is not NIL,
and the cell it points to is allocated. Let $S'$ be the store returned by sentinel insertion of
$x$ after $y$. Then for every cell $z$, either $z$ is empty in both $S$ and $S'$, or it holds a
node in both and the two nodes have the same payload, including keys and satellite data.
