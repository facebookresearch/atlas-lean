# Karlin–Altschul upper bound for two sequences

Let `p` and `q` be
[probability vectors](../../../../Probability/not-yet-classified/is-dist.md)
on a finite alphabet, `s` a real score on pairs of letters, and `θ ≥ 0` a root of
`∑_{a, b} p_a q_b e^{θ s(a, b)} = 1`, the
[moment generating function](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/score-mgf.md) of the
[pair score](pair-score.md) under the [pair law](pair-law.md). Then for all natural numbers `m` and
`n` and every `t > 0`, the [maximal ungapped alignment score](max-align-score.md) `M_{m,n}` of
independent words of `m` and `n` independent letters with laws `p` and `q` satisfies
`P(M_{m,n} ≥ t) ≤ m n e^{-θ t}`, the E-value bound. It is a union bound over the diagonals and
uses no independence between them: by the [single-diagonal law](two-prob-diag.md) and the
[one-sequence bound](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/score-prob-le-max-seg-score-le.md),
the maximal segment score of a diagonal of length `L` is at least `t` with probability at most
`L e^{-θ t}`, and the [diagonal lengths add up to](sum-diag-len.md) `m n`. For `θ = 0`, which
always satisfies the equation, the bound is `m n`.
