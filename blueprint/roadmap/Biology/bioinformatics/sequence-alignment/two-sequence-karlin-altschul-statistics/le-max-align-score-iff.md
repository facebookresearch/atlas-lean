# A positive level is reached iff some diagonal reaches it

For a real score `s` on pairs of letters, words `u` and `v` and a real `t > 0`, the
[maximal ungapped alignment score](max-align-score.md) satisfies `t ≤ M(u, v)` if and only if
`t ≤ M_d` for some [offset](offsets.md) `d` with `-|u| < d < |v|`, where `M_d` is the
[maximal segment score](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/max-seg-score.md) of the
[diagonal of offset](diag.md) `d`.
