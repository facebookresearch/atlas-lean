# Log-det recovery is consistent almost surely on the i.i.d. GTR model

Let `ι` be a finite set of at least two states. Let every subset of `ι` be measurable. Let
`π : ι → ℝ` have `π i > 0` for every `i` and `∑_i π i = 1`, let `s` be a symmetric real `ι × ι`
matrix with `s i j > 0` for `i ≠ j`, and let `t > 0`. Write `Q` for the
[GTR rate matrix](../../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`. Then for almost every sequence `ω` under the
[sample law](sample-law.md) `S` of `(π, s, t)`, the law of i.i.d. site pairs, the
[log-det rate estimate](../log-det-estimation-of-the-gtr-rate-matrix/rate-estimate.md) `R` and the
[log-det distance](../log-det-estimation-of-the-gtr-rate-matrix/log-det-distance.md) `Δ` of the
[empirical divergence matrix](../log-det-estimation-of-the-gtr-rate-matrix/empirical-divergence.md)
`F̂ₙ(ω)` of the first `n` site pairs `ω 0, …, ω (n - 1)` satisfy `R(F̂ₙ(ω)) → (-tr Q)⁻¹ · Q` and
`Δ(F̂ₙ(ω)) → -t · tr Q` as `n → ∞`.
