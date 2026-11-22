# Portfolio beta is linear in portfolio weights

On a probability space, let `R_i` be square-integrable returns of finitely many assets, `R_M` a
square-integrable market return with `Var(R_M) > 0`, and `w_i` real weights. Then the beta of the
portfolio return `∑_i w_i R_i` is the weighted sum of the asset betas:
`β(∑_i w_i R_i) = ∑_i w_i β(R_i)`, where `β(X) = Cov(X, R_M) / Var(R_M)`. The proof uses that the
covariance is additive and homogeneous in its first argument.
