# Number of diagonals with a segment scoring above a threshold

For a real score `s` on pairs of letters, natural numbers `m` and `n`, a real `t` and words `u` and
`v`, the exceedance count `W` is the number of [offsets](offsets.md) `d` with `-m < d < n` such
that the [maximal segment score](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/max-seg-score.md) of the
[diagonal of offset](diag.md) `d` of `u` and `v` is greater than `t`. For words of lengths `m`
and `n` it is the number of diagonals of their grid that contain a segment scoring more than `t`.
