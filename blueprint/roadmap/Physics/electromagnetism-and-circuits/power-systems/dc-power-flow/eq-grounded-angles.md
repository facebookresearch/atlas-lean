# With b > 0 on a connected network, grounded solutions are unique

Let a network have finitely many nodes and finitely many branches `e`, each with a tail and a head
node, and real branch susceptances `b_e`. Suppose that `b_e > 0` for every branch, that the network
is connected (the
[graph of the branches](../../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/positive-arc-graph.md),
in which two distinct nodes are adjacent when a branch joins them in either direction, is
connected),
and let `r` be a reference node. For injections `p`, every `θ` with `θ_r = 0` and `L_b θ = p`, where
the weighted Laplacian `L_b = B diag(b) Bᵀ` ([definition](weighted-laplacian.md)), `B` being the
incidence matrix with `(Bᵀ θ)_e = θ_tail(e) - θ_head(e)`, equals the
[grounded angles](grounded-angles.md).
