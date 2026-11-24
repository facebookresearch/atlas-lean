# Selected covariance blocks

**Selected covariance blocks** (Aitken 1934, (7), in regression form). Let `μ` be a
probability measure on `Ω`, let `X : Ω → ℝ^p` and `E : Ω → ℝ^q` be measurable and independent
under `μ`, let every coordinate of `E` be square-integrable under `μ`, and let
`Y = a + B X + E` for a vector `a : ℝ^q` and a matrix `B : ℝ^{q×p}`. Let the selection density
`w : ℝ^p → [0, ∞]` be measurable with `∫⁻ w(X) dμ = 1`, and let every coordinate of `X` be
square-integrable under the selected measure `ν = w(X) · μ`. Then for all coordinates `i`, `j`,
* `Cov_ν(X_i, Y_j) = ∑_k Cov_ν(X_i, X_k) B_{jk}`, and
* `Cov_ν(Y_i, Y_j) = ∑_k ∑_l B_{ik} Cov_ν(X_k, X_l) B_{jl} + Cov_μ(E_i, E_j)`.

## Sources

- Aitken (1934), p. 109, equation (7); Lawley (1943).
