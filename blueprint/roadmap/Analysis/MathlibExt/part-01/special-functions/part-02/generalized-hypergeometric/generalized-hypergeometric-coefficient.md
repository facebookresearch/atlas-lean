---
article_id: af_7369ee35610d4c3a99b7ed8e
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient
---

# Generalized Hypergeometric Coefficient

The coefficient of `z ^ n` in the generalized hypergeometric series `ₚF_q`
with upper parameters `a` and lower parameters `b`:

`(n ! : K)⁻¹ * ∏_{x ∈ a} (x)ₙ * (∏_{y ∈ b} (y)ₙ)⁻¹`

where `(x)ₙ = (ascPochhammer K n).eval x`.

Division is by totalized inverses in `K`; a zero lower product or factorial
cast yields `0`.  No analytic claim is made at singular lower parameters, and
the factorial cast may vanish in positive characteristic.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.GeneralizedHypergeometric](../../../../../../../sources/v2/MathlibExt.md)
