# Aipw Score

The **AIPW score** for the mean of an outcome `Y` observed on the response event `R`, with a
fixed response propensity `π` and a fixed outcome regression `m`:
`ψ = m(X) + 1_R (Y - m(X)) / π(X)`.

Convention at `π(x) = 0`: Lean sets `a / 0 = 0`, so on a stratum with `π(x) = 0` the score is
`m(X)` (the residual term is dropped), and the factor `e(x) / π(x) - 1` of
`integral_aipwScore_eq` is `-1`. In ordinary notation the score is undefined there.
