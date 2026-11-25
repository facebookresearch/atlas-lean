# Optimality of the minimum-variance portfolio

If the covariance matrix `S` is positive definite and the expected returns `μ_i` are not all
equal, then every portfolio `w` feasible for the target return `m` (`∑_i w_i = 1` and
`∑_i μ_i w_i = m`) has variance `wᵀ S w` at least that of the minimum-variance portfolio
`w* = Bᵀ (1, m)`, `B = (Mᵀ S⁻¹ M)⁻¹ Mᵀ S⁻¹` with `M = [1 μ]`.
