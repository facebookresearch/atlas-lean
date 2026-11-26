# Kernel of the weighted Laplacian of nonnegative connected networks

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed), with real
branch susceptances `b_e` and `L_b` the [susceptance-weighted Laplacian](weighted-laplacian.md).
Suppose that `b_e ≥ 0` for every branch `e` and that some node `r` is joined to every node by a walk
in the
[graph of positive-susceptance branches](../../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/positive-arc-graph.md),
in which distinct nodes are adjacent when some branch with `b_e > 0` joins them in either
orientation. Then for every real angle vector `θ`, `L_b θ = 0` if and only if `θ_v = θ_r` for every
node `v`: the kernel of `L_b` consists of the constant vectors. This is a special case of the
[kernel of the weighted Laplacian of an arc network connected from a root](../../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/weighted-laplacian-mul-vec-eq-zero-iff-o.md).
