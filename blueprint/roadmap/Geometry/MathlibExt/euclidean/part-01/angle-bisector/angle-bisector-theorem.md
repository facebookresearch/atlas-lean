---
article_id: af_f012205fe3a92d1a04a43c99
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.angle_bisector_theorem
---

# Angle bisector theorem

Forward direction of the Angle bisector theorem: if `AD` internally bisects
angle `A` of triangle `ABC` with `D` strictly between `B` and `C`, then
`BD / DC = AB / AC`. Source: https://en.wikipedia.org/wiki/Angle_bisector_theorem
(statement_id `angle-bisector-theorem`, required clause 1).
It follows from `angle_bisector_theorem_general`; the hypotheses `hAB`, `hAC` and `hAD` are
unused and keep the source's shape.
Proves `Wanted` entry `angle_bisector_theorem`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Angle bisector theorem general](angle-bisector-theorem-general.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.AngleBisector](../../../../../../sources/v2/MathlibExt.md)
