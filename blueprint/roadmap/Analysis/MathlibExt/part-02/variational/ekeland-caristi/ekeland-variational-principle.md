---
article_id: af_e18ac07614f5191d2bc61a23
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.ekeland_variational_principle
---

# Ekeland variational principle

Existence of `ε`-approximate minimizer with perturbed minimality.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Ekeland variational principle general](ekeland-variational-principle-general.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Variational.EkelandCaristi](../../../../../../sources/v2/MathlibExt.md)
- I. Ekeland, J. Math. Anal. Appl. 47 (1974), 324-353, DOI 10.1016/0022-247X(74)90025-0. It follows from `ekeland_variational_principle_general`; the instance `[Nonempty X]` is unused and keeps the source's shape. Proves `Wanted` entry `ekeland_variational_principle`.
