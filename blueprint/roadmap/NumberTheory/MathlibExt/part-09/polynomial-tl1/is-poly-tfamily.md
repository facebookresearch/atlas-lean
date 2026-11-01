---
article_id: af_4acba4771f378bbe6abbc8ab
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsPolyTFamily
---

# Is Poly TFamily

Predicate characterizing the polynomial family `T_{l-1}` of degree `l - 1`
(canonical name `polynomial T_{l-1}`, concept_id `jis_sem_267c1cca81c8b3a0062a0742`,
statement `jis_d5c7f2eca643e293a3405354`, source `jis_source_34b829866c2fa232064ad7c0`):
`T 0 = 0` (i.e. `T_{-1}(x) := 0`), degree clause for `l ≥ 1` with `T l ≠ 0`,
and the antiderivative clause `2 * sqrt x * T_l(x)` has derivative
`(8 * x ^ l - S_l(x)) / (sqrt x * (4 - x))` on `0 < x < 4`,
i.e. `T_{l-1}(x) = (x ^ (-1/2) / 2) ∫ integrand dx`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [TIntegrand](tintegrand.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PolynomialTL1](../../../../../sources/v2/MathlibExt.md)
