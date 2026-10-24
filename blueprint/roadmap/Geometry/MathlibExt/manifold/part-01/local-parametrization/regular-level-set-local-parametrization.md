---
article_id: af_ad2a07014ec3e0369e513b8c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Geometry.Manifold.LocalParametrizationWanted.regularLevelSet_localParametrization
---

# Regular Level Set local Parametrization

Local parametrization theorem: near a point where the differential is surjective, a level
set of a `C¹` map is the image of a `C¹` immersion. Sources: undergrad.yaml
`Submanifolds of R^n / local parameterization` (missing); J. Lee, Introduction to Smooth
Manifolds, 2nd ed., Ch. 4 (rank theorem).

Proof: Apply the implicit function theorem in adapted linear coordinates, then use a smooth bump
to extend the local graphing function globally. A shear chart makes its graph map an immersion.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists local Graph of surjective fderiv](../local-graph/exists-local-graph-of-surjective-fderiv.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Manifold.LocalParametrization](../../../../../../sources/v2/MathlibExt.md)
