# Exact recovery of the GTR rate matrix up to scale

Let `ι` be a finite set of states. Let `π : ι → ℝ` have `π i > 0` for every `i`, let `s` be a
symmetric real `ι × ι` matrix with `s i j ≥ 0` for `i ≠ j`, and let `t` be a real number with
`t ≠ 0`. Write `Q` for the
[GTR rate matrix](../../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`, and `F = diag (π) · exp (t · Q)`, with entries
`F i j = π i · exp (t · Q) i j`, for the true divergence matrix of a GTR branch of length `t`. Then
the [log-det rate estimate](rate-estimate.md) `R(F)` of the true divergence matrix is
`R(F) = (-tr Q)⁻¹ · Q`. When some `s i j` with `i ≠ j` is positive, `tr Q < 0` and this is the rate
matrix normalized to trace `-1`. When `s` vanishes off the diagonal, `Q = 0` and, with the
convention `0⁻¹ = 0`, both sides are `0`, of trace `0`.
