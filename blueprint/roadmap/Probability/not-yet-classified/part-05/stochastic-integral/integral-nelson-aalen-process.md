# Mean of the Nelson–Aalen estimator under vanishing risk

`E[Âₙ] = ∑_{k < n} Δα_{k+1}
P(Y_{k+1} ≠ 0)`. So `Â` is unbiased for `Λ*`; its bias for the cumulative hazard `αₙ - α₀` is
`-∑ Δα_{k+1} P(Y_{k+1} = 0)`, which vanishes in particular when the risk set is a.s. non-empty.
