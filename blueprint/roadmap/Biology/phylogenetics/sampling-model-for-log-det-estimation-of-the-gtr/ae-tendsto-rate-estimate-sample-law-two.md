# Log-det recovery on two states is consistent almost surely

On the two states `0` and `1`, let the base frequencies satisfy `π 0 > 0`, `π 1 > 0` and
`π 0 + π 1 = 1`, let `s` be a symmetric real `2 × 2` matrix with `s 0 1 = s 1 0 > 0`, and let
`t > 0`. Write `Q` for the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`. Then for almost every sequence `ω` under the
[sample law](sample-law.md) `S` of `(π, s, t)`, the law of i.i.d. two-state site pairs, the
[log-det rate estimate](../log-det-estimation-of-the-gtr-rate-matrix/rate-estimate.md) `R` and the
[log-det distance](../log-det-estimation-of-the-gtr-rate-matrix/log-det-distance.md) `Δ` of the
[empirical divergence matrix](../log-det-estimation-of-the-gtr-rate-matrix/empirical-divergence.md)
`F̂ₙ(ω)` of the first `n` site pairs `ω 0, …, ω (n - 1)` satisfy `R(F̂ₙ(ω)) → (-tr Q)⁻¹ · Q` and
`Δ(F̂ₙ(ω)) → -t · tr Q` as `n → ∞`.
