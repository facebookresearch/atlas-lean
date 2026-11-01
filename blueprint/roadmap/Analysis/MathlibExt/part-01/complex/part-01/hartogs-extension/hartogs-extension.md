---
article_id: af_aabe997937a9cec976e7fdbe
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.HartogsWanted.hartogs_extension
---

# Hartogs extension

Let `U ⊆ ℂⁿ` be open connected with `2 ≤ n`, `K ⊆ U` compact with `U \ K` connected. Every `f : ℂⁿ
→ ℂ` holomorphic on `U \ K` extends to holomorphic `F` on `U` with `Set.EqOn F f (U \ K)`. Here
`ℂⁿ` is `EuclideanSpace ℂ (Fin n)`. Source: Hartogs extension phenomenon, F. Hartogs, Math. Ann.
62 (1906); see Hörmander, An Introduction to Complex Analysis in Several Variables; Lean is ℂⁿ n ≥
2 finite-dimensional form via EuclideanSpace ℂ (Fin n) with U open connected K compact U\K
connected.

Proof: The compactly supported Cauchy–Green equation in one coordinate, combined with a smooth
cutoff and one-variable identity continuation.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Bar Deriv](bar-deriv.md)
- [Continuous On fderiv of differentiable On](continuous-on-fderiv-of-differentiable-o.md)
- [Differentiable At of bar Deriv eq zero](differentiable-at-of-bar-deriv-eq-zero.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.HartogsExtension](../../../../../../../sources/v2/MathlibExt.md)
