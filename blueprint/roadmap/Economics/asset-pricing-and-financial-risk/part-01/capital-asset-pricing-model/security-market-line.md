# A Sharpe-maximal market portfolio gives the security market line

Consider finitely many assets with a symmetric positive definite covariance matrix `S` of their
returns, expected returns `μ` and a risk-free return `r`, and let the Sharpe ratio of portfolio
weights `w` be `(μᵀ w - r) / √(wᵀ S w)`. Suppose the market portfolio `w_M` is fully invested
(`∑_i (w_M)_i = 1`), has a positive risk premium `μᵀ w_M - r > 0`, and has the largest Sharpe
ratio among all portfolios whose weights sum to `1`. Then every asset `i` lies on the security
market line `μ_i - r = β_i (μᵀ w_M - r)`, where `β_i = (S w_M)_i / (w_Mᵀ S w_M)`.
