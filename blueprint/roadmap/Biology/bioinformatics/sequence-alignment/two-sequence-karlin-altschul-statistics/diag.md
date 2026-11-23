# Scores along the diagonal with a given offset

For a real score `s` on pairs of letters, words `u` and `v` and an integer `d`, the diagonal of
offset `d` is the list of the scores `s(u_i, v_j)` over the cells `(i, j)` of the grid with
`j - i = d`, in increasing order of `i`: the [diagonal list](diag-from.md) from the cell
`((-d)⁺, d⁺)`, where `x⁺ = max(x, 0)`. Its length is the [diagonal length](diag-len.md)
`min(|u| - (-d)⁺, |v| - d⁺)`, and it is [empty](diag-eq-nil.md) unless `-|u| < d < |v|`.
