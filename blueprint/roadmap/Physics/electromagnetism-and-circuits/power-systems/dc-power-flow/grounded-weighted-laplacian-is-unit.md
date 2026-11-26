# Invertible grounded Laplacian of nonnegative connected networks

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed), with real
branch susceptances `b_e` and `L_b` the [susceptance-weighted Laplacian](weighted-laplacian.md).
Suppose that `b_e ≥ 0` for every branch `e` and that the reference node `r` is joined to every node
by a walk in the
[graph of positive-susceptance branches](../../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/positive-arc-graph.md),
in which distinct nodes are adjacent when some branch with `b_e > 0` joins them in either
orientation. Then the matrix `L_b^{(r)}`, indexed by the nodes other than `r` and obtained from
`L_b` by deleting the row and the column of `r`, is invertible: it has a two-sided inverse. This
follows from its [positive definiteness](grounded-weighted-laplacian-pos-def.md).
