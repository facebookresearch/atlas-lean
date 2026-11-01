---
article_id: af_ac7f87e9711d06eebc67e190
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.angle_bisector_converse
---

# Angle bisector converse

Converse of the Angle bisector theorem: a point `D` on segment `BC`
dividing `BC` in the ratio `AB : AC` lies on the internal bisector of angle `A`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Angle bisector converse general](angle-bisector-converse-general.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.AngleBisector](../../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Angle_bisector_theorem (statement_id `angle-bisector-theorem`, required clause 2). It follows from `angle_bisector_converse_general`; the hypotheses `hAB`, `hAC` and `hAD` are unused and keep the source's shape. Proves `Wanted` entry `angle_bisector_converse`.
