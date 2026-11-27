# Covariance of two SFS entries

Let `μ` be a probability measure on a measurable space `(Ω, F)`, let `m ⊆ F` be a sub-σ-algebra,
let `θ` be a real number, and let `ξ_i` and `L_i` (`i ∈ ℕ`) be real random variables with the
[conditional moments of the site frequency spectrum](sfscond-moments.md) given `m`: for all
`i, j ∈ ℕ`, `ξ_i` and `L_i` are square integrable, and almost surely `E[ξ_i | m] = (θ / 2) L_i`
and `E[ξ_i ξ_j | m] = (θ / 2)² L_i L_j + δ_{ij} (θ / 2) L_i`. Then for all `i, j ∈ ℕ`, by the
law of total covariance,

`Cov(ξ_i, ξ_j) = δ_{ij} (θ / 2) E[L_i] + (θ / 2)² Cov(L_i, L_j)`.

For `i ≠ j` the covariance comes entirely from the covariance of the branch lengths (Fu 1995).
