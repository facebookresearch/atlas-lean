# Branch-flow coefficient matrix of the DC model

For buses `v`, branches `e` with tail and head buses and real susceptances `b_e`, the branch-flow
matrix is `diag(b) Bᵀ`, where `B` is the incidence matrix with `(Bᵀ θ)_e = θ_tail(e) - θ_head(e)`.
Applied to angles `θ` it gives the [DC branch flow](../dc-power-flow/dc-branch-flow.md)
`f_e = b_e (θ_tail(e) - θ_head(e))` ([branch flows](branch-flow-matrix-mul-vec.md)).
