---
article_id: af_b2e561af907f449833362584
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.casey_theorem_cyclic_order
---

# Casey theorem cyclic order

Casey's theorem for four circles in genuine cyclic order: circles with centers `c1`, `c2`,
`c3`, `c4` and radii `r1`, `r2`, `r3`, `r4` tangent internally to a fixed outer circle with
center `O` and radius `R`, whose centers lie in directions `θ1 < θ2 < θ3 < θ4 < θ1 + 2π` from
`O`, with pairwise outer common tangent lengths `t12`, `t23`, `t34`, `t41`, `t13`, `t24`
satisfying `t12 * t34 + t23 * t41 = t13 * t24`. Unlike `MetaMathlibExt.casey_theorem`, a
consecutive angular gap may be at least `π`.
See https://en.wikipedia.org/wiki/Casey%27s_theorem.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Casey theorem cyclic order core](casey-theorem-cyclic-order-core.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.CaseyTheoremCyclicOrder](../../../../../../sources/v2/MathlibExt.md)
