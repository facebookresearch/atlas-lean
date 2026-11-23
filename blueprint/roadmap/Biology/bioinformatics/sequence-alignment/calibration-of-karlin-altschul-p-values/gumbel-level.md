# Gumbel threshold for a significance level

For real numbers `K`, `θ` and `α`, the Gumbel level is `x_α = log(K / (-log(1 - α))) / θ`. For
`K > 0`, `θ > 0` and `0 < α < 1` it is the centred threshold at which the Gumbel distribution
function `exp(-K e^{-θ x})` [equals `1 - α`](exp-neg-mul-exp-gumbel-level.md), and for `n ≥ 1` the
[Karlin–Altschul p-value](gumbel-pvalue.md) of a score `s` is at most `α` exactly when
`s ≥ log n / θ + x_α` ([rejection region](gumbel-pvalue-le-iff.md)). The definition is total, with
the conventions `log 0 = 0`, `log x = log |x|` and `x / 0 = 0`: for example `x_α = 0` when `α = 0`,
when `α = 1` and when `θ = 0`.
