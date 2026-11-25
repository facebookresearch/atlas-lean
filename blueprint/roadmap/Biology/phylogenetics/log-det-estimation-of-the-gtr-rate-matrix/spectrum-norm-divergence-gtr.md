# The normalized divergence at the truth has positive eigenvalues

Let `ι` be a finite set of states. Let `π : ι → ℝ` have `π i > 0` for every `i`, let `s` be a
symmetric real `ι × ι` matrix with `s i j ≥ 0` for `i ≠ j`, and let `t` be any real number. Write
`Q` for the [GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with
base frequencies `π` and exchangeabilities `s`, and `F = diag (π) · exp (t · Q)`, with entries
`F i j = π i · exp (t · Q) i j`, for the true divergence matrix of a GTR branch of length `t`. Then
every eigenvalue of the [normalized divergence matrix](norm-divergence.md) `N(F)` of `F` is
positive: `N(F)` is the exponential of a symmetric matrix.
