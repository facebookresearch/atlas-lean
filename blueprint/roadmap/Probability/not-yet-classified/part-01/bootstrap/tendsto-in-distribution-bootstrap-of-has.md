# Bootstrap validity for a smooth function of the mean (deterministic data)

Under the hypotheses of `tendstoInDistribution_bootMean`, if moreover the sample means converge
to `θ` and `g` is strictly differentiable at `θ` with derivative `g'`, then, conditionally on
the data, the bootstrap statistic `√n (g(x̄*ₙ) - g(x̄ₙ))` converges in distribution to
`N(0, g'² v)`, the same limit as the sampling distribution of `√n (g(x̄ₙ) - g(θ))`.
