# Upper ladder sandwich for the maximal segment score

For a [ladder-good](is-ladder-good.md) path of real scores, a natural number `n` and a real `t`, if
the [heights](excursion-height.md) `Y_i` of the excursions `i ≤ Nₙ` (the
[ladder count](ladder-count.md)) are all at most `t`, then the
[maximal segment score](max-segment-score.md) `Mₙ` of the first `n` scores is at most `t`; that is,
`Mₙ ≤ max_{i ≤ Nₙ} Y_i`. A segment `[a, b)` starts in some excursion `k` and ends in an excursion
`j ≥ k` with `j ≤ Nₙ`; the walk does not go below its value at the start of excursion `k` inside it,
and the ladder values decrease, so the segment score is at most `S_b - S_{T_j} ≤ Y_j`.
