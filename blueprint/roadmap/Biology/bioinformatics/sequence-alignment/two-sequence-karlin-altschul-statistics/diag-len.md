# Length of a diagonal of a grid

For natural numbers `m` and `n` and an integer `d`, the diagonal length is
`min(m - (-d)⁺, n - d⁺)`, where `x⁺ = max(x, 0)` and the subtraction is truncated
(`a - b = 0` for `b ≥ a`). It is the number of cells `(i, j)` with `0 ≤ i < m`, `0 ≤ j < n` and
`j - i = d`, the length of the [diagonal of offset](diag.md) `d` of two words of lengths `m` and
`n`; it is `0` unless `-m < d < n`.
