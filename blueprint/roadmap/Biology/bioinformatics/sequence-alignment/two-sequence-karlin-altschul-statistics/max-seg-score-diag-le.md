# No diagonal segment scores more than the maximal alignment score

For a real score `s` on pairs of letters, words `u` and `v` and every integer `d`, the
[maximal segment score](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/max-seg-score.md) of the
[diagonal of offset](diag.md) `d` is at most the
[maximal ungapped alignment score](max-align-score.md) `M(u, v)`: the best contiguous run of the
diagonal is the score of an ungapped alignment, or `0` if the run is empty.
