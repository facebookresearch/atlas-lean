# For t ≥ 0, maximal alignment score at most t iff no diagonal exceeds t

For a real score `s` on pairs of letters, words `u` and `v` and a real `t ≥ 0`, the
[maximal ungapped alignment score](max-align-score.md) `M(u, v)` is at most `t` if and only if,
for every [offset](offsets.md) `d` with `-|u| < d < |v|`, the
[maximal segment score](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/max-seg-score.md) of the
[diagonal of offset](diag.md) `d` is at most `t`: no diagonal contains a segment scoring more than
`t`.
