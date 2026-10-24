---
article_id: af_1b775f663dd0ca469341d1b5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.brahmagupta_area
---

# Brahmagupta Area

Brahmagupta's formula (https://en.wikipedia.org/wiki/Brahmagupta%27s_formula): a cyclic
    quadrilateral with sides `a`, `b`, `c`, `d` and semiperimeter `s` has area
    `√((s - a) * (s - b) * (s - c) * (s - d))`. Vertices `P Q R S` lie in the
    Euclidean plane; cyclicity is stated via a circumcenter `O` at equal
    distance from all four vertices; convex cyclic order `P, Q, R, S` is enforced
    by an interior diagonal-intersection point `T` lying strictly inside both
    segments `P-R` and `Q-S` (dist-additivity with positive parts); `A` is the
    polygon area, stated as the triangle-sum of the two Heron areas over the
    diagonal `e = dist P R`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.BrahmaguptaArea](../../../../../sources/v2/MathlibExt.md)
