---
article_id: af_08e315e00ab60c82c06e4626
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.ekeland_variational_principle_general
---

# Ekeland variational principle general

Ekeland variational principle without the `[Nonempty X]` assumption, which the point `x₀`
already provides: an `ε`-approximate minimizer `x₀` of a bounded-below lower semicontinuous `f`
on a complete metric space yields `xε` with `f xε ≤ f x₀`, `dist xε x₀ ≤ 1`, and
`f xε < f y + ε * dist xε y` for every `y ≠ xε`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Variational.EkelandCaristi](../../../../../../sources/v2/MathlibExt.md)
