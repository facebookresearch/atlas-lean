---
article_id: af_7a37e1a712666c7b5eafca33
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.pompeiu
---

# Pompeiu

Pompeiu's theorem (statement_id `pompeiu-s1`): an equilateral triangle `ABC` and a point
`P` in its plane not coinciding with a vertex satisfy that `PA`, `PB`, `PC` form the sides
of a (possibly degenerate) triangle. See https://en.wikipedia.org/wiki/Pompeiu%27s_theorem.
It follows from `pompeiu_general`; the vertex exclusion `hP` is unused (the source allows any
point `P`) and keeps the `Wanted` statement's shape.
Proves `Wanted` entry `pompeiu`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Pompeiu general](pompeiu-general.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.Pompeiu](../../../../../../sources/v2/MathlibExt.md)
