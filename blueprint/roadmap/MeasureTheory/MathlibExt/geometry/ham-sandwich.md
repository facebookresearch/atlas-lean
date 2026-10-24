---
article_id: af_6df5973ac9656036a1ba6c9f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.MeasureTheory.Geometry.HamSandwichWanted.ham_sandwich
---

# Ham Sandwich

For `0 < n`, every `n`-family of finite Borel measures on `EuclideanSpace ℝ (Fin n)` with `μ i ≪
volume` admits a unit vector `v` and `t : ℝ` bisecting each measure into two half-spaces of equal
mass `μ i univ / 2`. Source: A. H. Stone and J. W. Tukey, Duke Math. J. 9 (1942) 356–359 ham
sandwich theorem; J. Matoušek, Using the Borsuk–Ulam Theorem; Lean states measure-theoretic
Euclidean specialization with `μ i ≪ volume` making the bisecting hyperplane null.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Borsuk Ulam](../../../Topology/MathlibExt/homotopy/borsuk-ulam.md)

## Sources

- [MathlibExt, MathlibExt.MeasureTheory.Geometry.HamSandwich](../../../../sources/v2/MathlibExt.md)
