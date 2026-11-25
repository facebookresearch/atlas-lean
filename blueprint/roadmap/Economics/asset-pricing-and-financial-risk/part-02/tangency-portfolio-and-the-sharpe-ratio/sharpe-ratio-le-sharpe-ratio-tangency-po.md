# Tangency portfolio maximizes the Sharpe ratio for r below the GMV mean

For a positive definite covariance matrix `S` of at least one asset, expected returns `μ` and a
risk-free return `r` below `μ_GMV = (1ᵀ S⁻¹ μ) / (1ᵀ S⁻¹ 1)`, every fully invested portfolio `w`
(`∑_i w_i = 1`) has Sharpe ratio `(μᵀ w - r) / √(wᵀ S w)` at most that of the tangency portfolio
`z / (1ᵀ z)`, `z = S⁻¹ (μ - r 1)`.
