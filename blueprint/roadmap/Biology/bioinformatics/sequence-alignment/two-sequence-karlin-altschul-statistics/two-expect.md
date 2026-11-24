# The two-sequence model: weighted average over pairs of words

For real weights `p` and `q` on a finite alphabet, natural numbers `m` and `n` and a real functional
`F` of two words, the two-sequence average is the iterated [word average](word-expect.md)
`∑_u ∑_v p_{u₀} ⋯ p_{u_{m-1}} q_{v₀} ⋯ q_{v_{n-1}} F(u, v)` over the words `u` of length `m` and `v`
of length `n`. When `p` and `q` are
[probability vectors](../../../../Probability/not-yet-classified/is-dist.md),
it is the expectation of `F(u, v)` for independent words `u` and `v` of independent letters with
laws `p` and `q`; for other weights it is a weighted sum, which need not be an expectation.
