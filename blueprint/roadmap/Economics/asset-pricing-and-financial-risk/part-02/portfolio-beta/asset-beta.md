# Beta of a return relative to the market return

The beta of a return `X` against a market return `Y` under a measure `μ` is the ratio
`β = Cov(X, Y) / Var(Y)`. It is defined for every measure `μ` and all real functions `X` and `Y`,
with these conventions: `Cov(X, Y) = ∫ (X - E[X]) (Y - E[Y]) dμ` with `E[X] = ∫ X dμ`, where the
integral of a non-integrable function is `0`; `Var(Y) = ∫ (Y - E[Y])² dμ`, set to `0` when this
integral is infinite; and `x / 0 = 0`. It is the beta of `X` in the usual (CAPM) sense when `μ`
is a probability measure, `X` and `Y` are square-integrable and `Var(Y) > 0`.
