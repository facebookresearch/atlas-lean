# Tangency portfolio minimizes the Sharpe ratio for r above the GMV mean

For a positive definite covariance matrix `S` of at least one asset, expected returns `μ` and a
risk-free return `r` above `μ_GMV = (1ᵀ S⁻¹ μ) / (1ᵀ S⁻¹ 1)`, the tangency portfolio
`z / (1ᵀ z)`, `z = S⁻¹ (μ - r 1)`, has Sharpe ratio at most that of every fully invested
portfolio `w` (`∑_i w_i = 1`), the Sharpe ratio of `w` being `(μᵀ w - r) / √(wᵀ S w)`.
