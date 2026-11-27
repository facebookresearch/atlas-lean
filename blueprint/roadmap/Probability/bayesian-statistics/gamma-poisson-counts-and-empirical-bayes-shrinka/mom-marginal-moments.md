# Fisher consistency of the moment estimates

For `a > 0`, `b > 0` and `s > 0`, let `E = ∑_k k m(k)` and `W = ∑_k k² m(k) − E²` be the mean and
the variance of the [marginal law](marginal-lik-eq-neg-binomial-real.md) `m = NB(a, s a / b)`, sums
over `k ∈ ℕ`. Then the moment estimates at these population moments return the true hyperparameters:
the [shape estimate](mom-shape.md) is `E² / (W − E) = a` and the [rate estimate](mom-rate.md) is
`s E / (W − E) = b`.
