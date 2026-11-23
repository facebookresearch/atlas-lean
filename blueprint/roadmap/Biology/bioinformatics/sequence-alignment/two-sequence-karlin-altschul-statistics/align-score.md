# Align Score

The score of the **ungapped alignment** of `u` from position `i` with `v` from position `j`,
with **length bound** `ℓ`: `∑_{k < ℓ'} s(u_{i+k}, v_{j+k})` over the
`ℓ' = min ℓ (min (|u| - i) (|v| - j))` pairs that exist. Windows running past the end of a
sequence are truncated (`take`, `zipWith`), so `ℓ` bounds the alignment length rather than
fixing it (`alignScore_eq_min`); for `i + ℓ ≤ |u|` and `j + ℓ ≤ |v|` it is the score of the two
windows of length `ℓ`.
