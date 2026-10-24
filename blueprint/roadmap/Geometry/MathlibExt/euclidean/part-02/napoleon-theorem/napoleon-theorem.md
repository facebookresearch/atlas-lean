---
article_id: af_61a631727d1c5a0a32141c85
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.napoleon_theorem
---

# Napoleon theorem

Napoleon's theorem (outer version): for any nondegenerate (non-collinear)
triangle `ABC` in the Euclidean plane, with equilateral triangles erected outward
on each side, the centers (centroids) of the three outer equilateral triangles form
an equilateral triangle. Equilateral is stated via equal pairwise distances.
`A2` is the outer vertex on side `BC`, `B2` on side `CA`, `C2` on side `AB`;
`G1`, `G2`, `G3` are the corresponding centroids `(B + C + A2) / 3`,
`(C + A + B2) / 3`, `(A + B + C2) / 3`. Nondegeneracy is
`((B - A) × (C - A)) ≠ 0` via `ofLp` coordinates. Outward erection is pinned by
requiring each apex to lie strictly on the opposite side of its base line from the
remaining vertex, stated as the product of the two signed areas being `< 0`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Napoleon theorem general](napoleon-theorem-general.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.NapoleonTheorem](../../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Napoleon%27s_theorem (statement id `napoleon-s1`; raw: "Outer equilateral-triangle centers on any triangle form an equilateral triangle."). It follows from `napoleon_theorem_general`, which also shows the common distance is positive; the hypotheses `A ≠ B`, `B ≠ C`, `C ≠ A` and nondegeneracy are unused and keep the source's shape. Proves `Wanted` entry `napoleon_theorem`.
