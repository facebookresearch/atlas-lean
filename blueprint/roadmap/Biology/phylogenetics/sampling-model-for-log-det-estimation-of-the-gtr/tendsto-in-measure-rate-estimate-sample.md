# Log-det recovery is consistent in probability on the i.i.d. GTR model

Let `ι` be a finite set of at least two states. Let every subset of `ι` be measurable. Let
`π : ι → ℝ` have `π i > 0` for every `i` and `∑_i π i = 1`, let `s` be a symmetric real `ι × ι`
matrix with `s i j > 0` for `i ≠ j`, and let `t > 0`. Write `Q` for the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`. Then, under the [sample law](sample-law.md) `S` of
`(π, s, t)`, the law of i.i.d. site pairs, which is a probability measure, every entry of the
[log-det rate estimate](../log-det-estimation-of-the-gtr-rate-matrix/rate-estimate.md) `R` of the
[empirical divergence matrix](../log-det-estimation-of-the-gtr-rate-matrix/empirical-divergence.md)
`F̂ₙ(ω)` of the first `n` site pairs `ω 0, …, ω (n - 1)` converges in probability to the
corresponding entry of `(-tr Q)⁻¹ · Q`: for all states `i`, `j` and every `ε > 0`,
`S {ω : |R(F̂ₙ(ω)) i j - ((-tr Q)⁻¹ · Q) i j| ≥ ε} → 0` as `n → ∞`. Likewise the
[log-det distance](../log-det-estimation-of-the-gtr-rate-matrix/log-det-distance.md) `Δ` satisfies
`S {ω : |Δ(F̂ₙ(ω)) + t · tr Q| ≥ ε} → 0`.
