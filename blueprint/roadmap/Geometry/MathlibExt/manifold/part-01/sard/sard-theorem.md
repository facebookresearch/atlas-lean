---
article_id: af_75f818da9d3ca4bd7c39f8fa
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Geometry.Manifold.SardWanted.sard_theorem
---

# Sard theorem

If `M` is finite-dimensional Hausdorff second-countable boundaryless `C^∞` and `f : M → ℝ^n` is
`C^∞`, then the set of critical values has `volume` zero. Source: A. Sard, Bull. Amer. Math. Soc.
48 (1942) 883–890 measure of critical values; J. Lee, Introduction to Smooth Manifolds, 2nd ed.;
Guillemin-Pollack, Differential Topology; Lean states finite-dimensional manifold to
`EuclideanSpace ℝ (Fin n)` specialization.

## Depends on

- [Critical Values](critical-values.md)

## Proof depends on

- [Critical Set](critical-set.md)
- [Image Null](../../../../../MeasureTheory/MathlibExt/measure/measure-image-null-of-locally-null.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Manifold.Sard](../../../../../../sources/v2/MathlibExt.md)
