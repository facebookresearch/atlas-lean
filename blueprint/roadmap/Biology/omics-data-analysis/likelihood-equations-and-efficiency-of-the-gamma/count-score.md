# Count Score

The score of one count `k` at size factor `σ` in the hyperparameter `θ = (a, b)` (prior
shape `θ 0`, prior rate `θ 1`): the gradient
`(∑_{j<k} 1 / (a + j) + log b - log (b + σ), a / b - (a + k) / (b + σ))` of
`log (marginalLik a b σ k)`. Summed over a sample it is `(shapeScore, rateScore)`
(`sum_countScore`).
