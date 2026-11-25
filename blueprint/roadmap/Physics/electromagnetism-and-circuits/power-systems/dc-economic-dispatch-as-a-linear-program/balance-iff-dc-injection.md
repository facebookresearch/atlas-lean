# Nodal balance equals the DC injection balance

For every network with real susceptances `b`, generators at buses, demand `d`, generation `p` and
angles `θ`, `L_b θ = C p - d` holds if and only if the
[DC injection](../dc-power-flow/dc-injection.md) `B f` of the branch flows `f = diag(b) Bᵀ θ` equals
`C p - d`, where `L_b` is the [weighted Laplacian](../dc-power-flow/weighted-laplacian.md)
`L_b = B diag(b) Bᵀ` and `C` the [generator incidence](generator-incidence.md).
