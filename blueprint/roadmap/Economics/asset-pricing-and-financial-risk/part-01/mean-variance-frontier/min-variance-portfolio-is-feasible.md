# Minimum-variance portfolio is feasible

If the covariance matrix `S` is positive definite and the expected returns `μ_i` are not all
equal, then for every target return `m` the minimum-variance portfolio
`w* = Bᵀ (1, m)`, `B = (Mᵀ S⁻¹ M)⁻¹ Mᵀ S⁻¹` with `M = [1 μ]`, satisfies the budget and mean
constraints: `∑_i w*_i = 1` and `∑_i μ_i w*_i = m`.
