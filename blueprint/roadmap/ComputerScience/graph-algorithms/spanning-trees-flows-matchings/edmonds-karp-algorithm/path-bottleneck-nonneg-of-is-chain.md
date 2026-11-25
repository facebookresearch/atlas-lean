# Bottlenecks of residual chains are nonnegative

If consecutive entries of a vertex list $p$ are residual arcs of an integer flow matrix $f$ for capacities $c$, then the bottleneck of $p$, the minimum residual capacity $c(u, v) - f(u, v)$ over its steps, is nonnegative: positive when $p$ has at least one step, and $0$ by convention on shorter lists.

It supplies the nonnegative augmentation amount needed by [Proposition 2](residual-graph-edge-augment.md), including the degenerate case where source and sink coincide.
