# No other feasible portfolio attains the minimum variance

If the covariance matrix `S` is positive definite and the expected returns `μ_i` are not all
equal, then a portfolio `w` feasible for the target return `m` (`∑_i w_i = 1` and
`∑_i μ_i w_i = m`) whose variance `wᵀ S w` does not exceed that of the minimum-variance portfolio
`w* = Bᵀ (1, m)`, `B = (Mᵀ S⁻¹ M)⁻¹ Mᵀ S⁻¹` with `M = [1 μ]`, is `w*`.
