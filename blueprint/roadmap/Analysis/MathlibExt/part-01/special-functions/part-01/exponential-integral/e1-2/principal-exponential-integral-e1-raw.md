---
article_id: af_57ecbb63aabd3cf7e0bc2fc4
declaration: def
origin: cited
statement: formalized
lean: Complex.principalExponentialIntegralE1Raw
---

# Principal Exponential Integral E1 Raw

Totalized principal-`E1` kernel `Ein z - Log z - γ`.

This is a junk-value extension: at `z = 0` it evaluates to `-γ` via
`Complex.log 0 = 0`, not to the classical principal `E1`, which is singular
there. Use `principalExponentialIntegralE1` with a `z ≠ 0` proof for the
domain-safe API.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Ein](../../entire-exponential-integral/ein.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.ExponentialIntegral.E1](../../../../../../../../sources/v2/MathlibExt.md)
