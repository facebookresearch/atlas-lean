# Injections of the form L_b θ are balanced

Let a network have finitely many nodes and finitely many branches `e`, each with a tail and a head
node, and real branch susceptances `b_e`. For all real angles `θ` and injections `p` with
`L_b θ = p`, where the weighted Laplacian `L_b = B diag(b) Bᵀ`
([definition](weighted-laplacian.md)), `B` being the incidence matrix with
`(Bᵀ θ)_e = θ_tail(e) - θ_head(e)`, the injections sum to zero: `Σ_v p_v = 0`. No sign condition on
`b` is needed.

In particular, the [DC nodal injections](dc-injection.md) `p = B f`, with the
[DC branch flows](dc-branch-flow.md) `f_e = b_e (θ_tail(e) - θ_head(e))`, sum to zero over all nodes
for all real susceptances and angles, since `B f = L_b θ`
([identity](dc-injection-eq-weighted-laplacian-mul-v.md)): the injection at any node, the reference
node included, is minus the sum of the injections at the other nodes.
