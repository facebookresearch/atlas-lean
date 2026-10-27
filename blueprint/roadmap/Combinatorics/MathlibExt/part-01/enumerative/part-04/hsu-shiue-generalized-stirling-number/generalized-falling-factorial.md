---
article_id: af_658c0b102c8d812288722b76
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.generalizedFallingFactorial
---

# Generalized Falling Factorial

Generalized factorial with increment `alpha`: `(z | alpha) 0 = 1` and
for `n >= 1`, `(z | alpha) n = z (z - alpha) ... (z - n * alpha + alpha)`,
via the recursion `F (n + 1) = F n * (z - n * alpha)`
(source statement jis_7e7402faeeffb59e829d97bc).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.HsuShiueGeneralizedStirlingNumber](../../../../../../../sources/v2/MathlibExt.md)
