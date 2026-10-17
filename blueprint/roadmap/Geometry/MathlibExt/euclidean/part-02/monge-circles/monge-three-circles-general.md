---
article_id: af_68a38bec00c4abe3d9a2fc7e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.monge_three_circles_general
---

# Monge three circles general

Algebraic identity behind Monge's three-circle theorem: for points `c₁`, `c₂`, `c₃` of a real
vector space and pairwise distinct real weights `r₁`, `r₂`, `r₃` of any sign, the three points
`(rᵢ - rⱼ)⁻¹ • (rᵢ • cⱼ - rⱼ • cᵢ)` are collinear.
The circle reading needs positive weights: read as the radii of circles centered at the `cᵢ`,
they make these points the external homothety centers of the circle pairs. For two weights of
opposite sign the point is the internal similarity center of the circles of radii `|rᵢ|` and
`|rⱼ|`; e.g. `r₁ = -1`, `r₂ = 2` gives `(3 : ℝ)⁻¹ • (c₂ + 2 • c₁)`. `monge_three_circles` is the
statement for circles with positive radii in the plane.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.MongeCircles](../../../../../../sources/v2/MathlibExt.md)
