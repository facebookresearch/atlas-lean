# Injections of the form L_b θ are balanced

Let a network have finitely many nodes and finitely many branches `e`, each with a tail and a head
node, and real branch susceptances `b_e`. For all real angles `θ` and injections `p` with
`L_b θ = p`, where the weighted Laplacian `L_b = B diag(b) Bᵀ`
([definition](weighted-laplacian.md)), `B` being the incidence matrix with
`(Bᵀ θ)_e = θ_tail(e) - θ_head(e)`, the injections sum to zero: `Σ_v p_v = 0`. No sign condition on
`b` is needed.
