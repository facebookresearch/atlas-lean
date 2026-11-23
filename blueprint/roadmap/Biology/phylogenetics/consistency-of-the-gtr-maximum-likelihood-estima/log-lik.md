# Log-likelihood criterion

Let `σ` be a finite set of site patterns and `law` a map from a set `Θ` to the functions `σ → ℝ`.
The log-likelihood criterion of the model at frequencies `f : σ → ℝ` is
`L(f, θ) = ∑_a f a · log (law θ a)`. At the
[empirical site-pattern frequencies](../consistency-of-minimum-distance-gtr-estimators/empirical-freq.md)
of a sample it is the average log-likelihood of the sample; for a probability vector `f = law θ₀` it
is the expected log-likelihood under `law θ₀`. It is defined for all real values of `law`, with the
conventions `log 0 = 0` and `log x = log |x|` for `x < 0`; the intended domain is a positive model,
`law θ a > 0` for all `θ` and `a`.
