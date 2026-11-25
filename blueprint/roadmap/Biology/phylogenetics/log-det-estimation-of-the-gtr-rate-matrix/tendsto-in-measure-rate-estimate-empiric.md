# Log-det recovery is consistent in probability from aligned site pairs

Let `ι` be a finite set of at least two states. Let `π : ι → ℝ` have `π i > 0` for every `i`, let
`s` be a symmetric real `ι × ι` matrix with `s i j > 0` for `i ≠ j`, and let `t` be a real number
with `t > 0`. Write `Q` for the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`, and `F = diag (π) · exp (t · Q)`, with entries
`F i j = π i · exp (t · Q) i j`, for the true divergence matrix of a GTR branch of length `t`. Let
every subset of `ι` be measurable, let `P` be a finite measure on `Ω`, and let the aligned site
pairs `X 0, X 1, …` be measurable maps `Ω → ι × ι` that are pairwise independent and identically
distributed under `P` with the GTR divergence law `P (X 0 = (i, j)) = π i · exp (t · Q) i j` for all
states `i`, `j`. Then, entry by entry, the [log-det rate estimate](rate-estimate.md) `R` of the
[empirical divergence matrix](empirical-divergence.md) `F̂ₙ(ω)` converges in `P`-measure to
`(-tr Q)⁻¹ · Q`: for all states `i`, `j` and every `ε > 0`,
`P {ω : |R(F̂ₙ(ω)) i j - ((-tr Q)⁻¹ · Q) i j| ≥ ε} → 0` as `n → ∞`. Likewise the
[log-det distance](log-det-distance.md) `Δ` satisfies `P {ω : |Δ(F̂ₙ(ω)) + t · tr Q| ≥ ε} → 0`.
Pairwise independence forces the total mass of `P` to be `0` or `1`; as that mass is `∑_i π i > 0`,
`P` is a probability measure and `∑_i π i = 1`. So these are convergences in probability.
