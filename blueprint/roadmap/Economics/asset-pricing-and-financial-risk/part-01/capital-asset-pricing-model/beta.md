# Beta of an asset relative to a portfolio

For finitely many assets, a real square matrix `S` indexed by the assets and portfolio weights
`w_M`, the beta of asset `i` with respect to `w_M` is `(S w_M)_i / (w_Mᵀ S w_M)`. When `S` is the
covariance matrix of the asset returns, it is the covariance of asset `i`'s return with the
portfolio return divided by the portfolio variance. With the convention `x / 0 = 0` it is `0`
when `w_Mᵀ S w_M = 0`.
