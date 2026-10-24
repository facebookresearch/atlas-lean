---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CDIS.variance_estimator_optimal_le, CDIS.isMinOn_variance_optimalDensity, CDIS.variance_importanceSampling_estimator, CDIS.variance_importanceSampling, CDIS.isMinOn_optimal_density
---

# Optimal instrumental density

CDIS id 100. `g* = |h| f / ∫ |h| f` minimises the variance of the importance sampling
 estimator, for every sample size `n` (`CDIS.variance_estimator_optimal_le`). The estimator has
 variance `V_g((f / g) h) / n`, one term has variance `∫ (h f)² / g − (E_f h)²`, and `g*`
 minimises `∫ (h f)² / g` by Cauchy-Schwarz. The admissible `g` are the probability densities
 with `g > 0` wherever `h f ≠ 0` and `∫ (h f)² / g < ∞`; since `g*` vanishes where `h` does, the
 support condition is on `h f`, not on `f`.

## Depends on

- [Importance sampling](importance-sampling.md)

## Sources

- [Probabilités V, Densité optimale](../../sources/cdis-probabilites-v.md)
