# Bootstrap validity for smooth finite-dimensional statistics (deterministic data)

Under the hypotheses of `tendstoInDistribution_bootMeanVec`, if the sample means converge to
`θ` and `g : E → F` is strictly differentiable at `θ` with derivative `L`, then, conditionally
on the data, `√n (g(x̄*ₙ) - g(x̄ₙ))` converges in distribution to `L Z`; this is the delta-method
limit of `√n (g(x̄ₙ) - g(θ))` when `√n (x̄ₙ - θ) →ᵈ Z`.
