---
article_id: af_1d14f0450bfc75e319d71c89
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.finsler_hadwiger
---

# Finsler hadwiger

Finsler–Hadwiger theorem (shared-vertex squares, centers mid-segment standard
form): two nondegenerate squares `ABCD` and `AEFG` sharing the vertex `A`,
encoded via 90° rotation conditions with `C = B + D - A` and `F = E + G - A`;
with centers `O1 = (A + C) / 2`, `O2 = (A + F) / 2` and cross-segment midpoints
`P = (B + G) / 2`, `Q = (D + E) / 2`, the centers segment `O1O2` and the
mid-segment `PQ` are equal and perpendicular with a common midpoint.
This is the possibly degenerate identity: when the two squares coincide (`B = E`) both
segments are zero. `finsler_hadwiger_of_ne` adds `B ≠ E` and concludes `O1 ≠ O2`, so that
`O1 P O2 Q` is a square as in the source. The hypotheses `B ≠ A` and `E ≠ A` are unused and
keep the source's shape.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.FinslerHadwiger](../../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Finsler%E2%80%93Hadwiger_theorem (statement finsler-hadwiger-s1). Proves `Wanted` entry `finsler_hadwiger`.
