# Gaussian cross-covariance response

**Gaussian cross-covariance response** `Δz̄ = G P⁻¹ S`. Let `(A, Z)` be jointly
Gaussian with cross-covariance `Cov(A_i, Z_j) = G_ij` and `Cov(Z_i, Z_j) = P_ij`, `P`
positive definite, and select with measurable fitness weights `W(Z) ≥ 0` with
`0 < 𝔼[W(Z)]` and `W(Z) Z_j`, `W(Z) A_i` integrable. Then the selected shift of the
breeding values is `G P⁻¹` applied to the selection differential. This is the regression
identity behind Lande's equation; `selectedShift_breeding_eq_geneticCov` records the
form in which `G` is also the additive genetic covariance `Var(A)`.
