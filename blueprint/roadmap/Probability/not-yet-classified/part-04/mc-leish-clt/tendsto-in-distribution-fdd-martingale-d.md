# Finite-dimensional convergence of the step sums on `(0,1)`

**Finite-dimensional convergence of the step sums on `[0,1]`**, in the form of the
hypothesis `hT81` of the martingale functional CLT `tendstoInDistribution_arrayStepProcess`
(`MathlibExt.Probability.Martingale.MartingaleTightness`, roadmap task T82).

Row `n` of `ξ` is a square-integrable martingale difference sequence for `𝓕 n` (the array
hypotheses of T82) satisfying `LindebergConditionTriangular`. Three inputs that T82 does not
assume are explicit hypotheses here:
* `hRQV`: the realized quadratic variation `∑_{j < ⌊n t⌋} ξ n j²` tends to `t` in probability
  (T82 assumes the predictable form `∑_{j < ⌊n t⌋} E[ξ n j² | 𝓕 n j] → t`);
* `hZm`: `Z` is measurable (T82 assumes only `AEMeasurable Z P'`);
* `hZ`: `Z` has the centered Gaussian finite-dimensional laws of Brownian motion, covariance
  `min s u`.

Then for every finite set of times `I ⊆ [0,1]`,
`(∑_{i < ⌊n t⌋} ξ n i)_{t ∈ I} → (Z t)_{t ∈ I}` in distribution. This is
`tendstoInDistribution_fdd_martingale_lindeberg` with `N n t = ⌊n t⌋` and `A t = t`.
