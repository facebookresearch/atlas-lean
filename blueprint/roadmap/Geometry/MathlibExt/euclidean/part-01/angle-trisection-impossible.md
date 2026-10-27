---
article_id: af_894d7c63c0e5d04bc0ec2079
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.angle_trisection_impossible
---

# Angle Trisection Impossible

Impossibility of angle trisection (angle-trisection-s1): a real number is
constructible (straightedge and compass) iff it is obtainable from `ℚ` by
iterated quadratic extensions, and an angle is constructible iff its cosine is
constructible. The 60-degree angle cannot be trisected: `Real.cos (Real.pi / 9)`
(cosine of 20 degrees) is a root of the irreducible cubic
`8 * X ^ 3 - 6 * X - 1` over `ℚ`, hence not constructible, so no
straightedge-compass construction trisects every angle.
Spec correction applied upstream: the cubic is `8 * X ^ 3 - 6 * X - 1`
(not `+ 1`), since `cos (3 * 20°) = cos 60° = 1 / 2` gives `8 * c ^ 3 - 6 * c - 1 = 0`;
the `+ 1` variant has roots at `cos 40° / 80° / 160°`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.AngleTrisectionImpossible](../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Angle_trisection.
