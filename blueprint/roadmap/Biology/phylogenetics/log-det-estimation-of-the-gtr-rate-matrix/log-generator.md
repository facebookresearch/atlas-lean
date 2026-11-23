# Log-det generator

Let `ι` be a finite set of states. For a real `ι × ι` matrix `F` with
[base-frequency estimates](base-freq.md) `b(F) i = (∑_j F i j + ∑_j F j i) / 2` and
[normalized divergence matrix](norm-divergence.md) `N(F)`, the log-det generator is
`G(F) i j = (log N(F)) i j · √(b(F) j) / √(b(F) i)`, that is, `E log (N(F)) D` with
`D = diag (√ b(F))` and `E = diag ((√(b(F) i))⁻¹)`, the reciprocals taken entry by entry with
`0⁻¹ = 0`; `E = D⁻¹` when every `b(F) i > 0`. Here the real logarithm of a symmetric matrix applies
`log` to its eigenvalues in an orthonormal eigenbasis, with the conventions `log 0 = 0` and
`log x = log |x|` for `x < 0`. It is defined for every real `F`, with the conventions `√x = 0` for
`x ≤ 0` and `x / 0 = 0`: the entry `(i, j)` is `0` when `b(F) i ≤ 0` or `b(F) j ≤ 0`. The intended
domain is `b(F) i > 0` for every `i` with `N(F)` positive definite. At the
[true divergence matrix](log-generator-gtr.md) `diag (π) · exp (t · Q)` of a GTR branch, with
`π i > 0` for every `i` and `s` symmetric with `s i j ≥ 0` for `i ≠ j`, it equals `t · Q`, where `Q`
is the GTR rate matrix of `(π, s)`.
