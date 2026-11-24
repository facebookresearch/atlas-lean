# Chemotactic instability of the minimal Keller–Segel model

For `β > 0` and
`d_u, d_v ≥ 0`, at any homogeneous cell density `u₀` (steady state `(u₀, α u₀ / β)` by
`minimalKellerSegel_steadyState`, Jacobian `kellerSegelJacobian 0 α β` by
`jacobianMatrix_minimalKellerSegel`, diffusion matrix by `kellerSegelFlux_add`) the mode
`k ≠ 0` is unstable iff `d_u d_v k² < α χ u₀ - β d_u`.
