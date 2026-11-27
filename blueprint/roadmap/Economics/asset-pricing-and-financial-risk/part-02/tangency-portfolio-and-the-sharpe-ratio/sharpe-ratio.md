# Sharpe ratio of a portfolio

For finitely many assets with expected returns `μ`, covariance matrix `S` and risk-free return
`r`, the Sharpe ratio of a portfolio `w` is `(μᵀ w - r) / √(wᵀ S w)`, with the conventions
`√x = 0` for `x < 0` and `x / 0 = 0`: the ratio is `0` when `wᵀ S w ≤ 0`.
