# Gaussian response to selection, cross-covariance form

Let `ι` be a finite set of traits and let the breeding values `A` and the phenotypes `Z`, random
vectors in `ℝ^ι` on a probability space, be jointly Gaussian, with cross-covariance
`Cov(A_i, Z_j) = G_ij` and covariance `Cov(Z_i, Z_j) = P_ij`, where the matrix `P` is positive
definite. Let the fitness function `W` be measurable with `W ≥ 0` and `𝔼[W(Z)] > 0`, and let
`W(Z) Z_j` and `W(Z) A_i` be integrable for all `i, j`. Then the
[selected shift](selected-shift.md) of the breeding values is `Δz̄ = G P⁻¹ S`, where `S` is the
selected shift of `Z` (the selection differential). This is the regression identity behind
Lande's equation; the [genetic-covariance form](selected-shift-breeding-eq-genetic-cov.md) adds
the identification of `G` with the additive genetic covariance `Var(A)`.
