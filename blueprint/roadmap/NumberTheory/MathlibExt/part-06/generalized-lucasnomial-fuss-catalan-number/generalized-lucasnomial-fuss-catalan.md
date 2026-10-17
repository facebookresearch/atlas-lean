---
article_id: af_23585f37e41eb12c10fbd64d
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.generalizedLucasnomialFussCatalan
---

# Generalized Lucasnomial Fuss Catalan

Generalized Lucasnomial Fuss-Catalan number after Ballot, JIS Vol. 21:
`C_{U,a,r}(n) = (U_r / U_{(a-1)*n+r}) * binom{a*n+r-1}{n}_U`,
for `a >= 2`, `r >= 1`, `n >= 1`, over a parameterized Lucas sequence `U`.
Totalized over all naturals; bounds are documented, not enforced.
Concept `jis_sem_17c3c7bf3e94f23255e5a2a1`;
source SHA-256 `ca51d34e717a237b02bca4bfa28c57dfc15c81f1276c7634d5abe998d1c48b89`.

## Depends on

- [Lucas Parameters](../../part-07/lucas-polytopic-number/lucas-parameters.md)

## Proof depends on

- [Lucas Bracket](../../part-07/lucas-polytopic-number/lucas-bracket.md)
- [Lucasnomial](../../part-07/lucas-polytopic-number/lucasnomial.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.GeneralizedLucasnomialFussCatalanNumber](../../../../../sources/v2/MathlibExt.md)
