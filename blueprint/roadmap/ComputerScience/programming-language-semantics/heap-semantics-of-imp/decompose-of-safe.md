# Frame decomposition of heap executions

Let $h$ and $h_f$ be disjoint heaps, $c$ a heap
command and $s$ a store, and suppose that the configuration $(c, s, h)$ is safe. If
$(c, s, h \cup h_f)$ reaches $(c'', s'', h'')$ by finitely many (possibly zero) small steps, then
there is a heap $h_2$, disjoint from $h_f$, such that $(c, s, h)$ reaches $(c'', s'', h_2)$ by
finitely many small steps, $h'' = h_2 \cup h_f$, and $(c'', s'', h_2)$ is safe.

Safety supplies the step-existence that single-step decomposition needs at each stage.
