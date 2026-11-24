# Grounded DC load flow on a connected network with b > 0

Let a network have finitely many nodes and finitely many branches `e`, each with a tail and a head
node, and real branch susceptances `b_e`. Suppose that `b_e > 0` for every branch, that the network
is connected (the graph on the nodes in which two distinct nodes are adjacent when a branch joins
them, in either direction, is
[connected](../../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/positive-arc-graph.md)),
and let `r` be a reference node, and let the injections `p` be balanced, `Σ_v p_v = 0`. With the
weighted Laplacian `L_b = B diag(b) Bᵀ` ([definition](weighted-laplacian.md)), `B` being the
incidence matrix with `(Bᵀ θ)_e = θ_tail(e) - θ_head(e)` and `θ*` the
[grounded angles](grounded-angles.md):

- `θ*` is the unique `θ` with `θ_r = 0` and `L_b θ = p`;
- `θ*_r = 0` and `L_b θ* = p`;
- the [DC injection](dc-injection.md) `B f` of the branch flows of `θ*` is `p`;
- the [branch flows](dc-branch-flow.md) of `θ*` are `f_e = b_e (θ*_tail(e) - θ*_head(e))`, and every
  solution of `L_b θ = p` has the same flows;
- for every branch, `|P_e - f_e| ≤ b_e |θ*_tail(e) - θ*_head(e)|³ / 6`, where `P_e` is the
  [sending-end real power](ac-branch-real-power.md) of the lossless AC model with unit voltage
  magnitudes at the angles `θ*`.

The last bound compares two formulas at the same angles; it is not a comparison of two independently
solved operating points, and solvability says nothing about AC or reactive feasibility.
