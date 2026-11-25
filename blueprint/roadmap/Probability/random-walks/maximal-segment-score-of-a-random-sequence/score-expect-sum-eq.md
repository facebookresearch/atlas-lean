# Mean of the score sum

For a [probability vector](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md)
`q` and real scores `f` on a finite alphabet and every natural number `n`, the
[expectation](score-expect.md) of the sum `Sₙ` of the scores of `n` independent letters with law `q`
is `E[Sₙ] = n μ`, where `μ = ∑_b q_b f(b)` is the mean score.
