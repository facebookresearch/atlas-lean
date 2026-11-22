# Building a segment tree from a list

The segment tree built from a list $L$ with entries
in an additive monoid is the empty tree if $L$ is empty, and a single leaf with value $x$ if
$L = (x)$. If $L$ has length $n \ge 2$, it is the internal node whose left child is the tree built
from the first $\lfloor n/2 \rfloor$ entries of $L$, whose right child is the tree built from the
remaining entries, and which caches the aggregate of the left child plus the aggregate of the
right child, in that order, and the sum of the sizes of its children.
