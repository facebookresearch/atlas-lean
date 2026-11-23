# Weighted average of a functional over words of a given length

For real weights `p` on a finite alphabet, a natural number `n` and a real functional `G` of words,
the word average is `∑_w p_{w₀} ⋯ p_{w_{n-1}} G(w)`, the sum over all words `w = w₀ ⋯ w_{n-1}` of
length `n` weighted by their [background likelihood](../../position-weight-matrices/bg-lik.md). When
`p` is a
[probability vector](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md),
it is the expectation of `G(w)` for a word of `n` independent letters with law `p`; for other
weights it is a weighted sum, which need not be an expectation. For `n = 0` it is `G` of the empty
word.
