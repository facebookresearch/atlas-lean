# Frame decomposition of a single heap step

Let $h$ and $h_f$ be disjoint heaps, $c$ a heap
command and $s$ a store, and suppose that the configuration $(c, s, h)$ can take a small step. If
$(c, s, h \cup h_f)$ takes a small step to $(c', s', h'')$, then there is a heap $h_1$, disjoint
from $h_f$, such that $(c, s, h)$ takes a small step to $(c', s', h_1)$ and $h'' = h_1 \cup h_f$.

For a step that reads, writes or frees a cell, the step-existence hypothesis forces that cell to lie in $h$; an allocation step of $(c, s, h \cup h_f)$ picks an address fresh for $h \cup h_f$, hence fresh for $h$.
