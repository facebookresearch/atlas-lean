# Lande's multivariate response, genetic-covariance form

Let `ι` be a finite set of traits and let the breeding values `A` and the phenotypes `Z`, random
vectors in `ℝ^ι` on a probability space, be jointly Gaussian with `Cov(A_i, Z_j) = G_ij` and
`Cov(A_i, A_j) = G_ij` (so `G` is also the additive genetic covariance `Var(A)`, as when
`Z = A + E` with `Cov(A, E) = 0`), and with `Cov(Z_i, Z_j) = P_ij`, where `P` is positive
definite. Let the fitness function `W` be measurable with `W ≥ 0` and `𝔼[W(Z)] > 0`, and let
`W(Z) Z_j` and `W(Z) A_i` be integrable for all `i, j`. Then the
[selected shift](selected-shift.md) of the breeding values is `Δz̄ = G P⁻¹ S`, where `S` is the
selected shift of `Z`. This is a special case of the
[cross-covariance form](selected-shift-breeding-eq.md), which does not assume
`Cov(A_i, A_j) = G_ij`.
