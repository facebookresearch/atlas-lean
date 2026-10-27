---
article_id: af_57810831618ab86ed232f4a6
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.Ramanujan_master_theorem
---

# Ramanujan Master Theorem Wanted

Ramanujan's master theorem (statement id `ramanujan-master-s1`).

This specialization assumes `0 < a < b`, `a < re(s) < b`, analyticity of `φ`
on the half-plane `re(z) > -b`, and a uniform vertical exponential bound with
rate strictly below `π`.  For positive real `x`, `F x` is normalized by the
exponential generating series `sum φ(k) * (-x)^k / k!`; the displayed
integrability hypothesis supplies convergence of its Lebesgue Mellin integral
over `(0, ∞)`.  Complex powers use Mathlib's principal-log normalization.  Under
these hypotheses the integral equals `Gamma(s) * φ(-s)`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.SpecialFunctions.RamanujanMasterTheoremWanted](../../../../../sources/v2/WantedExt.md)
- https://en.wikipedia.org/wiki/Ramanujan%27s_master_theorem (Raw: `int_0^infty x^{s-1} sum_k phi(k)(-x)^k/k! dx = Gamma(s) phi(-s)`.)
