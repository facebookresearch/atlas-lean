# Score of an ungapped alignment with a length bound

For a real score `s` on pairs of letters, words `u` and `v` and natural numbers `i`, `j` and `ℓ`,
the score of the ungapped alignment of `u` from position `i` with `v` from position `j`, with
length bound `ℓ`, is `∑_{k < ℓ'} s(u_{i+k}, v_{j+k})`, where `ℓ' = min(ℓ, |u| - i, |v| - j)` with
truncated subtraction (positions are counted from `0`). Windows running past the end of a word are
cut, so `ℓ` bounds the alignment length rather than fixing it: the value is the score of the
alignment of length `ℓ'` ([cut length bound](align-score-eq-min.md)). For `i + ℓ ≤ |u|` and
`j + ℓ ≤ |v|` it is the score of the windows `u_i ⋯ u_{i+ℓ-1}` and `v_j ⋯ v_{j+ℓ-1}`. It is `0`
when `ℓ' = 0`, that is when `ℓ = 0`, `i ≥ |u|` or `j ≥ |v|`.
