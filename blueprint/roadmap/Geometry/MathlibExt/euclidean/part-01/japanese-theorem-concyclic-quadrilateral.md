---
article_id: af_5cacc02fe8f1b48231c83b83
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.japanese_theorem_concyclic_quadrilaterals
---

# Japanese Quads

Japanese theorem for concyclic quadrilaterals
(stable source: https://en.wikipedia.org/wiki/Japanese_theorem_for_concyclic_quadrilaterals,
statement id `japanese-quads-s1`): a convex cyclic quadrilateral with its two
triangulations (diagonals); inradii `r1`, `r2` of one pair of opposite
triangles (via incircles inscribed in triangles `ABC`, `CDA`) and `r3`, `r4`
of the other pair (via incircles inscribed in triangles `BCD`, `DAB`).
Then `r1 + r2 = r3 + r4`: the inradius sum is triangulation-independent.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Carnot inradius circumradius general](carnot-inradius/carnot-inradius-circumradius-general.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.JapaneseQuads](../../../../../sources/v2/MathlibExt.md)
