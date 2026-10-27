---
article_id: af_b3f62596188485630c645685
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Geometry.Manifold.SubmersionCompWanted.submersionAt_comp
---

# Submersion At comp

Composition of submersions at a point between Banach manifolds without boundary. Sources:
Mathlib `Mathlib/Geometry/Manifold/Submersion.lean` TODO (`IsSubmersionAt.comp`);
J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4.

Proof: Replace the first submersion's target chart by the second submersion's source chart, then
compose the two projection normal forms and use the product of their complements.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Comp](comp-2.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Manifold.SubmersionComp](../../../../../../sources/v2/MathlibExt.md)
