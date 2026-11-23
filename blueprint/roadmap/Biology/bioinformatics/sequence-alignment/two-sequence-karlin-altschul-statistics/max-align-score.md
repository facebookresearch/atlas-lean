# Maximal ungapped alignment score of two words

For a real score `s` on pairs of letters and words `u` and `v`, the maximal ungapped alignment
score `M(u, v)` is the largest [ungapped alignment score](align-score.md) with start positions
`i ≤ |u|` and `j ≤ |v|` and length bound `ℓ ≤ |u|`. Each such triple scores the alignment of two
windows of the same length `min(ℓ, |u| - i, |v| - j)`, and every pair of windows of `u` and `v` of
the same length arises this way, so `M(u, v)` is the best score of an ungapped alignment of a
window of `u` with a window of `v`, the empty alignment scoring `0`. In particular `M(u, v) ≥ 0`,
and `M(u, v) = 0` when `u` or `v` is empty.
