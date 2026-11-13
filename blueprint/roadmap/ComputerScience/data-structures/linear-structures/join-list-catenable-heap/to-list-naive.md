# Naive flattening of a catenable heap

The naive flattening of a catenable heap is defined
by recursion: the empty heap flattens to the empty list, the heap with an element $x$ added in
front of a heap $t$ flattens to $x$ followed by the naive flattening of $t$, and the join of
heaps $l$ and $r$ flattens to the naive flattening of $l$ followed by that of $r$.

It is the reference against which the accumulating flattening is checked.
