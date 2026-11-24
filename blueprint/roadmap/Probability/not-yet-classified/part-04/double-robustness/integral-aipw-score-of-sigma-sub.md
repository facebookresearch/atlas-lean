# Exact bias of the AIPW score

**Exact bias of the AIPW score** (a product of nuisance errors). Let `e* = P(T | m)`,
`μ₀* = E[Y₀ | m]` and `μ₁* = E[Y₁ | m]`. Under consistency, mean exchangeability, integrability
and `ε ≤ e ≤ 1 - ε`, for fixed `m`-measurable candidates `e, g₀, g₁`,
`E[ψ] - E[Y₁ - Y₀] = E[(e* - e) ((μ₁* - g₁) / e + (μ₀* - g₀) / (1 - e))]`.
This is a population identity at fixed nuisances, not a finite-sample statement about fitted
nuisances.
