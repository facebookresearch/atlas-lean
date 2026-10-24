---
article_id: af_0d104c9c76367f98a3a94b0b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Geometry.Manifold.ImmersionCompWanted.immersionAt_comp
---

# Immersion At comp

Composition of immersions at a point between Banach manifolds without boundary. Sources:
Mathlib `Mathlib/Geometry/Manifold/Immersion.lean` TODO (`IsImmersionAt.comp`);
J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4.

Proof: Restrict the first immersion's codomain chart to the second immersion's domain chart, then
conjugate that chart transition through the second linear normal form. The normal forms compose
with the product of their complements.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Comp](comp-2.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Manifold.ImmersionComp](../../../../../../sources/v2/MathlibExt.md)
