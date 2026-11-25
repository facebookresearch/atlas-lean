# Squared correlation of two random variables

For a measure `μ` on `Ω` and real functions `X` and `Y` on `Ω`, the squared correlation is

`corr²(X, Y) = Cov(X, Y)² / (Var X · Var Y)`,

with covariance and variances under `μ`. These are defined for all functions:
`Cov(X, Y) = ∫ (X - E X) (Y - E Y) dμ`, which is `0` when the integrand is not integrable, with
`E X = ∫ X dμ` equal to `0` for a non-integrable `X`; `Var X` is `∫ (X - E X)² dμ` when this is
finite and `0` when it is infinite; and with the convention `x / 0 = 0`, `corr²(X, Y) = 0` when
`Var X = 0` or `Var Y = 0`. For a probability measure and square-integrable `X` and `Y` with
positive variances, it is the fraction of the variance of `Y` explained by the best linear predictor
from `X`.
