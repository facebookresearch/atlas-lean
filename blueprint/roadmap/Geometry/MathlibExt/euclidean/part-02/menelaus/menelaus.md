---
article_id: af_72a30405ca24bda1deb83bfb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.menelaus
---

# Menelaus

Menelaus's theorem (statement ID menelaus-s1): a transversal meets the sidelines
of triangle `ABC` in collinear points iff the signed ratio product is `-1`.
See https://en.wikipedia.org/wiki/Menelaus%27s_theorem.
It follows from `menelaus_general`; the three `lineMap` incidence hypotheses (implied by the
ratio equations), `B ≠ C` and `A ≠ C` (implied by non-collinearity), and
`D ≠ B`, `D ≠ C`, `E ≠ C`, `E ≠ A`, `F ≠ A`, `F ≠ B` are unused and keep the source's shape.
Proves `Wanted` entry `menelaus`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Menelaus general](menelaus-general.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.Menelaus](../../../../../../sources/v2/MathlibExt.md)
