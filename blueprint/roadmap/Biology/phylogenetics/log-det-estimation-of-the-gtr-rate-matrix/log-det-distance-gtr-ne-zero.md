# Nonzero time and strictly positive rates give nonzero log-det distance

Let `ι` be a finite set of at least two states. Let `π : ι → ℝ` have `π i > 0` for every `i`, let
`s` be a symmetric real `ι × ι` matrix with `s i j > 0` for `i ≠ j`, and let `t` be a real number
with `t ≠ 0`. Write `Q` for the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`, and `F = diag (π) · exp (t · Q)`, with entries
`F i j = π i · exp (t · Q) i j`, for the true divergence matrix of a GTR branch of length `t`. Then
the [log-det distance](log-det-distance.md) `Δ(F)` of the true divergence matrix is nonzero:
`Δ(F) = -t · tr Q ≠ 0`.
