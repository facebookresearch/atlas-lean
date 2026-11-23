# `countScore` is the score of the marginal likelihood

For `σ > 0` and `θ` with positive
coordinates, `countScore σ θ k` is the gradient at `θ` of `t ↦ log (marginalLik (t 0) (t 1) σ k)`,
the score (`VectorInference.score`) of the negative binomial marginal family in `(a, b)`.
