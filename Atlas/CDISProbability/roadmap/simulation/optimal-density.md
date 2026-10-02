---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CDIS.isMinOn_optimal_density, CDIS.variance_importanceSampling
---

# Optimal instrumental density

CDIS id 100. The variance of one term is `∫ (h f)² / g − (E_f h)²`, and
 `g* = |h| f / ∫ |h| f` minimises `∫ (h f)² / g` by Cauchy-Schwarz.

## Depends on

- [Importance sampling](importance-sampling.md)

## Sources

- [Probabilités V, Densité optimale](../../sources/cdis-probabilites-v.md)
