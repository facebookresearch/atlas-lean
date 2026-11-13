# Exact bias of the AIPW score under MAR

For a covariate with finitely many values, the
score is integrable and
`E[ψ] = E[Y] + ∑ₓ (e(x) / π(x) - 1) (E[Y; X = x] - m(x) P(X = x))`, `e(x) = P(R | X = x)`.
Each term is the product of the response-propensity error and the regression error on the
stratum `X = x`. Neither positivity nor any condition on `π`, `m` is assumed; for `π(x) = 0`
the identity uses the convention in `aipwScore` (the factor is `-1`).
