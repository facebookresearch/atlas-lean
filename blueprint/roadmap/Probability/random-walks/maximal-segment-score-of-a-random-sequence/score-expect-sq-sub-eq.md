# Variance of the score sum

For a
[probability vector](../../not-yet-classified/is-dist.md)
`q` and real scores `f` on a finite alphabet and every natural number `n`, the sum `Sₙ` of the
scores of `n` independent letters with law `q` has variance `n σ²`:
`E[(Sₙ - n μ)²] = n ∑_b q_b (f(b) - μ)²`, where `μ = ∑_b q_b f(b)` is the mean score and
`σ² = ∑_b q_b (f(b) - μ)²` the variance of one score.
