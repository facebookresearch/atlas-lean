/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
public import MathlibExt.AlgebraicGeometry.StableLineMaps

/-!
# Fine degree-one stable-map moduli and their actual deformation complexes

This scope is genus zero, one marking, and degree one in complex projective
space of positive dimension. The source allows nodal stable maps; it does
not assume that every family is already a projective-line bundle. The
comparison must reconstruct the family from its actual rank-two coordinate
quotient followed by its actual marking line quotient.

The equivalence is normalized by the two canonical sheaf arrows, so a free
moduli carrier or an unrelated equivalence cannot satisfy the target. The
proper-base-change map is the literal adjoint of the pulled-back counit.
The obstruction and tangent statements use the actual direct images of the
Euler cokernel pulled to the stable-map curve.

Reference: Fulton--Pandharipande, *Notes on stable maps and quantum
cohomology*, https://arxiv.org/abs/alg-geom/9608011, §§1--3. Ordinary marked
prestable families, dual-graph stability and generic projective-bundle
constructions are already covered support and are excluded from the request.
Higher-degree/genus GW, DT objects and gluing/invariant theory remain outside
this fine degree-one comparison; no claims about those theories are made.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.StableLineMapComparisonWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
open MathlibExt.AlgebraicGeometry.StableLineMaps

variable (r : ℕ)
    (X : ProjectiveBundle Point 0 r (targetGenerators r))
    (T : ComplexScheme)

/-- The fine stable-map groupoid is the actual two-step quotient flag,
with both arrows fixed by coordinate adjunction and marking evaluation. -/
public def_wanted moduliComparison (_positive : 0 < r) [IsNoetherian T.left] :
    StableLineModuliComparison r X T

/-- Arbitrary scheme base change preserves the actual degree-one direct
image through its canonical counit-defined map. -/
public theorem_wanted quotient_base_change (_positive : 0 < r) [IsNoetherian T.left]
    (F : StableLineFamily r X T)
    (T' : ComplexScheme) [IsNoetherian T'.left] (h : T' ⟶ T)
    (F' : StableLineFamily r X T') (b : FamilyBaseChange F h F') :
    IsIso (quotientBaseChange F b)

/-- Relative projective-space convexity, with the coefficient sheaf kept
explicit and quasicoherent, kills the actual map obstruction sheaf. -/
public theorem_wanted relative_map_obstruction_vanishes (_positive : 0 < r)
    [IsNoetherian T.left] (F : StableLineFamily r X T)
    (J : T.left.Modules) [J.IsQuasicoherent] : IsZero (deformationModule F 1 J)

/-- The degree-zero part of the same actual deformation model has the
expected rank of maps from a parametrized projective line into projective space. -/
public theorem_wanted relative_map_tangent_bundle (_positive : 0 < r) [IsNoetherian T.left]
    (F : StableLineFamily r X T) :
    IsBundle (deformationModule F 0 (SheafOfModules.unit T.left.ringCatSheaf)) (2 * r + 1)

end WantedExt.AlgebraicGeometry.StableLineMapComparisonWanted
