# Forward Ornstein–Uhlenbeck marginal

The law at time `t` of the Ornstein–Uhlenbeck process
`dX = -X dt + √2 dB` started from `q`: the law of `e^{-t} X₀ + √(1 - e^{-2t}) Z` with `X₀ ∼ q` and
`Z` an independent standard Gaussian vector (Chen et al., arXiv:2209.11215v3, Section 2.1). Only
times `t ≥ 0` are meaningful: for `t < 0`, `1 - e^{-2t}` is negative and its `Real.sqrt` is `0`.
