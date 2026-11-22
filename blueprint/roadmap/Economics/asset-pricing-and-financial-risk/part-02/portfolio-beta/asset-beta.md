# Asset Beta

The formal beta ratio `cov[X, Y; μ] / Var[Y; μ]` of return `X` against
market return `Y` under `μ`. This is only a totalized expression: `μ` is an
arbitrary measure, `X` and `Y` are arbitrary functions, `cov` and
`Var` return junk values when their integrability conditions fail, and real
division by `0` gives `0`. It is the CAPM beta of `X` only when all of the
following hold: `μ` is a probability measure, `X` and `Y` are square-integrable
(`MemLp X 2 μ` and `MemLp Y 2 μ`), and `0 < Var[Y; μ]`. These are the
hypotheses of `portfolio_beta_linear`.
