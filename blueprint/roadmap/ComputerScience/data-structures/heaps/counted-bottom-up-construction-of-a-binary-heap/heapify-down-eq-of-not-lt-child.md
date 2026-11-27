# Heapify Down eq of not lt child

Let $a$ be a vector of size $n$, $i < n$ an index, and $j$ the child of $i$ selected by the canonical maximum-child selector. If $a_i$ does not compare less than $a_j$, the counted sift-down at $i$ returns $a$ unchanged at cost (comparisons, swaps) equal to the selector's cost plus $(1, 0)$: the parent comparison and no swap. The selector's cost is $(1, 0)$ when $i$ has a right child and $(0, 0)$ otherwise.
