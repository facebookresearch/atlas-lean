# Recovery of the exchangeabilities up to scale

Let `ι` be a finite set of states. Let `π : ι → ℝ` have `π i > 0` for every `i`, let `s` be a
symmetric real `ι × ι` matrix with `s i j ≥ 0` for `i ≠ j`, and let `t` be a real number with
`t ≠ 0`. Write `Q` for the
[GTR rate matrix](../../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`, and `F = diag (π) · exp (t · Q)`, with entries
`F i j = π i · exp (t · Q) i j`, for the true divergence matrix of a GTR branch of length `t`. Then
for all states `i ≠ j` the [log-det rate estimate](rate-estimate.md) `R(F)` and the
[base-frequency estimate](base-freq.md) `b(F) i = (∑_j F i j + ∑_j F j i) / 2` of the true
divergence matrix give back the exchangeability up to the common scale `-tr Q`:
`R(F) i j / b(F) j = (-tr Q)⁻¹ · s i j`. When `s` vanishes off the diagonal, `Q = 0` and, with the
convention `0⁻¹ = 0`, both sides are `0`.
