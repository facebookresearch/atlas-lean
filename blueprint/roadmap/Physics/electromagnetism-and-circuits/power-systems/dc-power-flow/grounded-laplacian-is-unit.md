# The reduced matrix of a connected network with b > 0 is invertible

Let a network have finitely many nodes and finitely many branches `e`, each with a tail and a head
node, and real branch susceptances `b_e`. Suppose that `b_e > 0` for every branch, that the network
is connected (the graph on the nodes in which two distinct nodes are adjacent when a branch joins
them, in either direction, is
[connected](../../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/positive-arc-graph.md)),
and let `r` be a reference node. Then the [reduced grounded matrix](grounded-laplacian.md), the
weighted Laplacian `L_b = B diag(b) Bᵀ` ([definition](weighted-laplacian.md)), `B` being the
incidence matrix with `(Bᵀ θ)_e = θ_tail(e) - θ_head(e)` with the row and column of `r` deleted, is
invertible.
