# Variance of a linear SFS statistic

Let `μ` be a probability measure on a measurable space `(Ω, F)`, let `m ⊆ F` be a sub-σ-algebra,
let `θ` be a real number, and let `ξ_i` and `L_i` (`i ∈ ℕ`) be real random variables with the
[conditional moments of the site frequency spectrum](sfscond-moments.md) given `m`: for all
`i, j ∈ ℕ`, `ξ_i` and `L_i` are square integrable, and almost surely `E[ξ_i | m] = (θ / 2) L_i`
and `E[ξ_i ξ_j | m] = (θ / 2)² L_i L_j + δ_{ij} (θ / 2) L_i`. Then for every finite set `s` of
natural numbers and all real coefficients `a_i`,

`Var(∑_{i ∈ s} a_i ξ_i) = (θ / 2) ∑_{i ∈ s} a_i² E[L_i] + (θ / 2)² Var(∑_{i ∈ s} a_i L_i)`.
