# Adding a frame heap preserves the ability to step

Let $h$ and $h_f$ be disjoint heaps,
$c$ a heap command and $s$ a store. If the configuration $(c, s, h)$ can take a small step, then
so can $(c, s, h \cup h_f)$.

Allocation may choose a different fresh address on the larger heap.
