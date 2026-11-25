# Weighted Laplacian with the reference row and column deleted

Let a network have finitely many nodes and finitely many branches `e`, each with a tail and a head
node, and real branch susceptances `b_e`, and let `r` be a reference node. The reduced grounded
matrix is the weighted Laplacian `L_b = B diag(b) Bᵀ` ([definition](weighted-laplacian.md)), `B`
being the incidence matrix with `(Bᵀ θ)_e = θ_tail(e) - θ_head(e)`, with the row and the column of
`r` deleted; it is indexed by the nodes other than `r`.
