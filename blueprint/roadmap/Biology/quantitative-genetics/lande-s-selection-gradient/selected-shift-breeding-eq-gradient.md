# Gaussian response to selection, cross-covariance gradient form

Let `ι` be a finite set of traits and let the breeding values `A` and the phenotypes `Z`, random
vectors in `ℝ^ι` on a probability space, be jointly Gaussian with `Cov(A_i, Z_j) = G_ij`, and let
`Z` have law `N(μ, P)` with `P` positive definite. Let the fitness function `W` be measurable,
bounded and nonnegative, with [mean fitness](mean-fitness-mv.md) `w̄(m) = ∫ W dN(m, P)` positive
at `m = μ`. Then the [selected shift](selected-shift.md) of the breeding values is
`Δz̄ = G ∇_μ log w̄(μ)`: the cross-covariance `G` applied to the gradient of `log w̄` at `μ`.
