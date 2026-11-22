# VaR of one loss is 0

At level `0.95`, the single loss (100 with probability 0.04)
has `VaR = 0`: the set `{x | 0.95 ≤ cdf x}` is `Ici 0`, whose infimum is `0`.

Proof route (not mandatory): unfold `valueAtRisk` and `cdfQuantile` (the level `95/100`
is in `Ioo 0 1`), show `{x | 95/100 ≤ cdf (lossLaw prodWeights loss1) x} = Ici 0` from
`cdf_loss_single_eq` (for `x < 0` the cdf is `0 < 0.95`; for `x ≥ 0` it is at least
`0.96 ≥ 0.95`), then `csInf_Ici`.
