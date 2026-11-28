# Weighted average over the score sequences of a given length

For real weights `q` and real scores `f` on a finite alphabet, a natural number `n` and a real
functional `F` of score lists, the average is
`E[F] = ∑_w q_{w₀} ⋯ q_{w_{n-1}} F(f(w₀), …, f(w_{n-1}))`, the sum over all words `w = w₀ ⋯ w_{n-1}`
of length `n` weighted by their [background likelihood](../../../Biology/bioinformatics/position-weight-matrices/bg-lik.md).
When `q` is a
[probability vector](../../not-yet-classified/is-dist.md),
it is the expectation of `F` of the scores of `n` independent letters with law `q`; for other
weights it is a weighted sum, which need not be an expectation. For `n = 0` it is `F` of the empty
list.
