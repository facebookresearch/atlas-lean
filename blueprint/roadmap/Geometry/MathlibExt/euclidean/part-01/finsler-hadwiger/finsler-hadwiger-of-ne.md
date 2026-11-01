---
article_id: af_06d09fd6ebedf931113c2f6e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.finsler_hadwiger_of_ne
---

# Finsler hadwiger of ne

Finsler–Hadwiger theorem for distinct squares: two squares `ABCD` and `AEFG` sharing the
vertex `A` (encoded as in `finsler_hadwiger`) with `B ≠ E`. The segments `O1O2` and `PQ`
between the centers and between the cross-segment midpoints are equal, perpendicular, share a
midpoint and are nonzero, so `O1 P O2 Q` is a square. This generalizes the source to possibly
degenerate input squares: `B ≠ A` and `E ≠ A` are not assumed, so one of `ABCD` and `AEFG` may
be the single point `A`, in which case `O1 P O2 Q` is a quarter of the other square.
`finsler_hadwiger` is the source-shaped, possibly degenerate form.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.FinslerHadwiger](../../../../../../sources/v2/MathlibExt.md)
