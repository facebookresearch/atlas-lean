# Single-score generating function as a pair-score generating function

For a [probability vector](../../not-yet-classified/is-dist.md)
`q` and real scores `f` on a finite alphabet and every real `θ`, the
[moment generating function](score-mgf.md) `∑_b q_b e^{θ f(b)}` equals the
[pair-score generating function](../../../Biology/bioinformatics/position-weight-matrices/pair-mgf.md)
`∑_a ∑_b q_a q_b e^{θ s(a, b)}` of the pair score `s(a, b) = f(a)`, which ignores the second letter.
