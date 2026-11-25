# Accumulating traversal of a ball tree

For a ball tree $T$ and a list $A$ of points, the
accumulating traversal returns $A$ when $T$ is empty, the point $p$ followed by $A$ when $T$ is a
leaf holding $p$, and, when $T$ is a node with children $L$ and $R$, the accumulating traversal of
$L$ whose accumulator is the accumulating traversal of $R$ with accumulator $A$.

The result is the leaf points of $T$, from left to right, followed by $A$.
