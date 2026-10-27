---
article_id: af_1f1d63f2ff6bc03d8da2048f
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Geometry.UlamWanted.Ulam.BodyOfRevolution.body
---

# Body

The convex body of revolution defined by a smooth concave function `f : ℝ → ℝ` supported on
`[-R₁, R₂]` is `K_f := { x ∈ ℝᵈ | x₁ ∈ [-R₁, R₂] and x₂² + ... + x²_d ≤ f(x₁)² }`.
Note: we actually index the `xᵢ` starting from zero, for convenience.

## Depends on

- [Body Of Revolution](body-of-revolution.md)

## Sources

- [WantedExt, WantedExt.Geometry.UlamWanted](../../../../../sources/v2/WantedExt.md)
