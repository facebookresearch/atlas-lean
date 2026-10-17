---
article_id: af_fbb61aa4f7952301fabb19d2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.casey_theorem
---

# Casey Theorem

Casey's theorem: four circles with centers `c1`, `c2`, `c3`, `c4` and radii
`r1`, `r2`, `r3`, `r4` tangent internally to a fixed outer circle with center `O`
and radius `R` in cyclic order, with pairwise outer common tangent lengths `t12`,
`t23`, `t34`, `t41`, `t13`, `t24` satisfying `t12 * t34 + t23 * t41 = t13 * t24`.
See https://en.wikipedia.org/wiki/Casey%27s_theorem.

Cyclic order is encoded by `hcyc12`, `hcyc23`, `hcyc34`, `hcyc41`: each consecutive pair of
centers makes a positive oriented angle at `O`, so every consecutive angular gap is strictly
less than `π`. Configurations with a gap of at least `π` are not covered; the general
cyclic-order statement is `MetaMathlibExt.casey_theorem_cyclic_order` in
`MathlibExt.Geometry.Euclidean.CaseyTheoremCyclicOrder`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.CaseyTheorem](../../../../../sources/v2/MathlibExt.md)
