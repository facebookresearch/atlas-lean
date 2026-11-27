# Closed-form Sharpe ratio of the tangency portfolio

For a positive definite covariance matrix `S` of at least one asset, expected returns `μ` and a
risk-free return `r` below `μ_GMV = (1ᵀ S⁻¹ μ) / (1ᵀ S⁻¹ 1)`, the tangency portfolio
`w = z / (1ᵀ z)`, `z = S⁻¹ (μ - r 1)`, has Sharpe ratio
`(μᵀ w - r) / √(wᵀ S w) = √((μ - r 1)ᵀ S⁻¹ (μ - r 1))`.
