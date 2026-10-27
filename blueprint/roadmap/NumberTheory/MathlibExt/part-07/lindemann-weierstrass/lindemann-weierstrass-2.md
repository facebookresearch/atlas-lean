---
article_id: af_734175a9554b09542c6cc2d8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.LindemannWeierstrassWanted.lindemann_weierstrass
---

# Lindemann weierstrass

If `α : ι → ℂ` is injective over a `Fintype ι` with `∀ i, IsAlgebraic ℚ (α i)`, then for any
algebraic coefficients `β : ι → ℂ` not all zero, `∑ i, β i * Complex.exp (α i) ≠ 0`. Source: F.
von Lindemann 1882 and K. Weierstrass, Zu Lindemann's Abhandlung Über die Ludolph'sche Zahl, 1885;
textbook in Baker, Transcendental Number Theory

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lindemann weierstrass'](lindemann-weierstrass.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.LindemannWeierstrass](../../../../../sources/v2/MathlibExt.md)
