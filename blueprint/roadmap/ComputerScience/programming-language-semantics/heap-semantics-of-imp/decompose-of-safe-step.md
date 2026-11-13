# Frame decomposition of a single heap step

Let $h$ and $h_f$ be disjoint heaps, $c$ a heap
command and $s$ a store, and suppose that the configuration $(c, s, h)$ can take a small step. If
$(c, s, h \cup h_f)$ takes a small step to $(c', s', h'')$, then there is a heap $h_1$, disjoint
from $h_f$, such that $(c, s, h)$ takes a small step to $(c', s', h_1)$ and $h'' = h_1 \cup h_f$.

The step-existence hypothesis forces any address the step touches to lie in $h$.
