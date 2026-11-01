---
article_id: af_38861cebe2f5efd083edea38
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Analysis.EulerLagrangeWanted.Analysis.IsVariationalExtremum
---

# Is Variational Extremum

A `C¹` path `x : ℝ → ℝ` is a **variational extremum** of the action
`I(y) := ∫_a^b L(t, y(t), y'(t)) dt` on `(a, b)` if for every smooth compactly
supported variation `h` with `tsupport h ⊆ (a, b)`, the first variation
`d/dε|_{ε=0} ∫_a^b L(t, x(t) + ε h(t), x'(t) + ε h'(t)) dt` vanishes.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.EulerLagrangeWanted](../../../../../sources/v2/WantedExt.md)
