# The pair-score generating function is the Karlin–Altschul one

For real weights `p` on a finite alphabet, a real score `s` on pairs of letters and a real `θ`,
the [moment generating function](../../../../Probability/random-walks/maximal-segment-score-of-a-random-sequence/score-mgf.md) of
the [pair score](pair-score.md) under the [pair law](pair-law.md) with the weights `p` on both
letters, `∑_{(a, b)} p_a p_b e^{θ s(a, b)}`, equals the Karlin–Altschul
[pair-score generating function](../../position-weight-matrices/pair-mgf.md)
`∑_a ∑_b p_a p_b e^{θ s(a, b)}`.
