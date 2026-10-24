---
article_id: af_f11691ddb97311023adc2694
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.BasicHypergeometric.basicHypergeometricCoefficient
---

# Basic Hypergeometric Coefficient

The coefficient of `z ^ n` in the general basic hypergeometric series `{}_rφ_s`.

This is DLMF 17.4.1 adapted from `_{r+1}φ_s` to `{}_rφ_s`: with `r` upper parameters
`a₁,…,aᵣ` and `s` lower parameters `b₁,…,bₛ`,

```
coeff n = (∏_i (a_i;q)_n) / ((q;q)_n ∏_i (b_i;q)_n) * ((-1)^n q^{n choose 2})^{1+s-r}
```

where `(a;q)_n = ∏_{j=0}^{n-1} (1 - a q^j)` and `(q;q)_n = ∏_{j=0}^{n-1} (1 - q^{j+1})`.
The factor `(-1)^n q^{n choose 2}` is `(-1 : ℂ)^n * q ^ Nat.choose n 2` and the outer
exponent `1 + s - r` is in `ℤ` via totalized `zpow` on `ℂ`.

Finite `q`-Pochhammer symbols are expanded directly as products. Division and integer powers
use Mathlib's totalized operations on `ℂ`; analytic applications must separately establish that
the denominator does not vanish.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.BasicHypergeometric](../../../../../../../sources/v2/MathlibExt.md)
