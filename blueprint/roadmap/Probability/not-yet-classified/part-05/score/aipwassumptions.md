# AIPWAssumptions

The identifying assumptions for the average treatment effect of a binary treatment `T` given
a covariate `X`, in primitive terms. With `σ(X) = MeasurableSpace.comap X m𝒳` and the true
propensity `π = μ[1_T | σ(X)]`:
* consistency: the observed outcome is `Y₁` on `T` and `Y₀` off it;
* mean exchangeability: `E[1_T Y₁ | X] = π E[Y₁ | X]` and `E[1_{Tᶜ} Y₀ | X] = P(Tᶜ | X) E[Y₀ | X]`
  (implied by `Y_a ⊥ T | X`);
* positivity (strong overlap): `ε ≤ π ≤ 1 - ε` almost surely, for some `ε > 0`.
