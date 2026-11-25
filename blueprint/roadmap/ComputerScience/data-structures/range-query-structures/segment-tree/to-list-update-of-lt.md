# Leaf list after an in-range point update

Let $t$ be a valid segment tree over an
additive monoid and let $i$ be a natural number less than the size of $t$. Then for every value
$y$, the leaf list of the point update of $t$ at $i$ with $y$ is the leaf list of $t$ with its
entry at position $i$ (counting from $0$) replaced by $y$.

Validity is what ties the cached sizes used for routing to the leaf list.
