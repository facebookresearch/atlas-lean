---
article_id: af_2ac5406ed824c8d345a0a610
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.napoleon_theorem_general
---

# Napoleon theorem general

Napoleon's theorem (outer version) with only the hypotheses the argument uses: if `ABC` is
a nondegenerate triangle in the Euclidean plane and `A2`, `B2`, `C2` are the apexes of equilateral
triangles erected outward on `BC`, `CA`, `AB`, then the centroids `G1`, `G2`, `G3` of those
triangles are pairwise at the same positive distance, so they form a nondegenerate equilateral
triangle. The hypotheses are those of `napoleon_theorem`, the source-shaped form, without
nondegeneracy (a factor of `hout3`) and `A ≠ B`, `B ≠ C`, `C ≠ A`, which follow from it.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.NapoleonTheorem](../../../../../../sources/v2/MathlibExt.md)
