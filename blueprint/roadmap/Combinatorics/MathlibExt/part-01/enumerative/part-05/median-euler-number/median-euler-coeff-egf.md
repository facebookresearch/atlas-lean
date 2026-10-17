---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.medianEulerCoeff_egf
---

# Median Euler Coeff egf

Exponential-generating-function identity: `(exp x + exp (-x))`, that is `2 cosh x`,
times the EGF of `medianEulerCoeff` equals `2 + exp x - exp (-x)`, the `sech x + tanh x`
series.

## Depends on

- [Median Euler Coeff](median-euler-coeff.md)

## Proof depends on

- [Median Euler Coeff succ](median-euler-coeff-succ.md)
- [Median Euler Coeff zero](median-euler-coeff-zero.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.MedianEulerNumber](../../../../../../../sources/v2/MathlibExt.md)
