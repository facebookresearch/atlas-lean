# Log-likelihood criterion

Let `σ` be a finite set of site patterns and `law` a map from a set `Θ` to the functions `σ → ℝ`.
The log-likelihood criterion of the model at weights `f : σ → ℝ` is the weighted sum
`L(f, θ) = ∑_a f a · log (law θ a)`, defined for all real `f` and `law` with the conventions
`log 0 = 0` and `log x = log |x|` for `x < 0`. Positivity of `law θ` makes every logarithm an
ordinary one; nonnegativity together with normalization, `∑_a law θ a = 1`, makes `law θ` a
probability vector; normalization alone does not, as `(2, -1)` sums to `1`. When `f` is any
probability vector, for example `f = law θ₀`, `L(f, θ)` is the expected value of `log (law θ a)`
under `f`; for general real weights it is only a weighted sum. At the
[empirical site-pattern frequencies](../consistency-of-minimum-distance-gtr-estimators/empirical-freq.md)
`p̂ₙ` of `n > 0` observed patterns it is the
[average of their log-values](log-lik-empirical-freq.md), and when `law θ` is a probability vector
positive at every observed pattern, `exp (n · L(p̂ₙ, θ))` is the product of the one-column
probabilities of the observed patterns. This product is the likelihood of the sample under the
product model, in which the columns are independent with common law `law θ`; without that model it
is only a product of one-column likelihoods. Without that positivity the criterion is not a
log-likelihood: a model giving an observed pattern probability `0` scores `0` for it, by the
convention `log 0 = 0`, and can beat a model of positive likelihood.
