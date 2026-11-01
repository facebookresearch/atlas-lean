---
article_id: af_853e06b3ddb93ebb9412166c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.viviani_general
---

# Viviani general

Viviani's theorem, general form (statement `viviani-s1`): an
equilateral triangle in the Euclidean plane and an interior point `P`;
the sum of the perpendicular distances from `P` to the three sides
equals the altitude of the triangle. No positivity hypothesis on the
side length is needed: membership of `P` in the ambient interior already
yields affine independence, hence nondegeneracy.

Proof: Following the barycentric-coordinate area decomposition in Wikipedia, "Viviani's theorem"
(Proof section), we express the three distances as barycentric weights times a common height.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.Viviani](../../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Viviani%27s_theorem.
