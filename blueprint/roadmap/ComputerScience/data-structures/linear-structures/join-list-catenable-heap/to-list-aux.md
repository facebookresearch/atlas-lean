# Accumulating flattening of a catenable heap

Given a catenable heap $h$ and a list $s$, the
accumulating flattening of $h$ onto $s$ is defined by recursion on $h$: for the empty heap it is
$s$; for the heap with an element $x$ added in front of a heap $t$ it is $x$ followed by the
accumulating flattening of $t$ onto $s$; for the join of heaps $l$ and $r$ it is the accumulating
flattening of $l$ onto the accumulating flattening of $r$ onto $s$.

Each node of $h$ is visited once.
