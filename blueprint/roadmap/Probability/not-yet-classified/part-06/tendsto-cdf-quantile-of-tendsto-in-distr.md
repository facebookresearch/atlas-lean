# Weak convergence implies quantile convergence

If `X n ⇒ Y` and the pushforward
limit CDF `F x = (Measure.map Y μ').real (Set.Iic x)` is continuous and strictly
increasing, the `q`-quantile (generalized inverse) of the law of `X n` tends to that of
`Y`, for fixed `q ∈ (0, 1)`, using the imported `cdfQuantile_le_iff` (Quantile.lean:77).
