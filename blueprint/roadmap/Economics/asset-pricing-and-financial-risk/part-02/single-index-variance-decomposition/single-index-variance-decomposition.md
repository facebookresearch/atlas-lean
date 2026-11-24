# Systematic plus idiosyncratic variance decomposition

On a probability space, let the market return `R_M` and the residual `ε` be square-integrable and
uncorrelated, `Cov(R_M, ε) = 0`. Then for all real `α` and `β` the single-index return
`R = α + β R_M + ε` has variance `Var(R) = β² Var(R_M) + Var(ε)`. The constant `α` drops out,
the cross term vanishes because `Cov(β R_M, ε) = β Cov(R_M, ε) = 0`, and the `β²` factor comes
from `Var(β R_M) = β² Var(R_M)`.
