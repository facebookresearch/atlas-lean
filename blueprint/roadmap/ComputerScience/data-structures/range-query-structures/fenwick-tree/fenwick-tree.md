# Fenwick tree

A Fenwick tree (binary indexed tree) over a commutative additive monoid
$\alpha$ is an array of elements of $\alpha$, read as one-indexed interval sums with an unused
dummy entry at index $0$. The structure itself imposes no condition on the entries, and the
underlying array it represents is not stored; the relation saying that a tree represents a
given array is defined separately.
