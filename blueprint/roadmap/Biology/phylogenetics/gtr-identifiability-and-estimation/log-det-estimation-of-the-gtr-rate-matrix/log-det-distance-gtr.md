# Exact recovery of the log-det distance

Let `ι` be a finite set of states. Let `π : ι → ℝ` have `π i > 0` for every `i`, let `s` be a
symmetric real `ι × ι` matrix with `s i j ≥ 0` for `i ≠ j`, and let `t` be any real number. Write
`Q` for the [GTR rate matrix](../../time-reversible-nucleotide-substitution-models/gtr-rate.md) with
base frequencies `π` and exchangeabilities `s`, and `F = diag (π) · exp (t · Q)`, with entries
`F i j = π i · exp (t · Q) i j`, for the true divergence matrix of a GTR branch of length `t`. Then
the [log-det distance](log-det-distance.md) `Δ(F)` of the true divergence matrix is
`Δ(F) = -t · tr Q`, the trace-normalized branch length. For `t ≥ 0` and base frequencies `π` summing
to `1`, a stationary probability vector, the expected number of substitutions per site is
`-t · ∑_i π i · Q i i`; in general this differs from `-t · tr Q`, although the two agree, for
example, when `t = 0` or `Q = 0`.
