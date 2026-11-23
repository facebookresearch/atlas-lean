# Normalized divergence matrix

Let `ι` be a finite set of states. For a real `ι × ι` matrix `F` with
[base-frequency estimates](base-freq.md) `b(F) i = (∑_j F i j + ∑_j F j i) / 2`, the normalized
divergence matrix is `N(F) i j = ((F i j + F j i) / 2) / (√(b(F) i) · √(b(F) j))`, that is,
`D⁻¹ F_s D⁻¹` with `F_s = (F + Fᵀ) / 2` and `D = diag (√ b(F))`. It is symmetric for every `F`. It
is defined for every real `F`, with the conventions `√x = 0` for `x ≤ 0` and `x / 0 = 0`: the
entries of row and column `i` are `0` when `b(F) i ≤ 0`. The intended domain is `b(F) i > 0` for
every `i`.
