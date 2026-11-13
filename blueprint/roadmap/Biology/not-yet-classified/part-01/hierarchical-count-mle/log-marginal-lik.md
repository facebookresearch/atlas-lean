# Log Marginal Lik

The log marginal likelihood of hyperparameters `(a, b)` (prior shape and rate) for counts
`kᵢ` observed at size factors `sᵢ`, one independent rate `λᵢ ~ Gamma(a, b)` per observation:
`ℓ(a, b) = ∑ᵢ log P(kᵢ ∣ a, b, sᵢ)`, with
`P(k ∣ a, b, s) = marginalLik a b s k = NB(a, s a / b)`.
