# Chebyshev bound for the score sum

For a [probability vector](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md)
`q` and real scores `f` on a finite alphabet, a natural number `n` and a real `t < n μ`, where
`μ = ∑_b q_b f(b)` is the mean score, the sum `Sₙ` of the scores of `n` independent letters with law
`q` satisfies `P(Sₙ < t) ≤ n σ² / (n μ - t)²`, with `σ² = ∑_b q_b (f(b) - μ)²`.
