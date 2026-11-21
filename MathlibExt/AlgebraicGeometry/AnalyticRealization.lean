/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The holomorphic-sheaf abbreviation follows AxiomMath/Weil, revision
27cdb2049be62ee2911429b47f54774078450e32,
Weil/Geometry/Manifold/Sheaf/Holomorphic.lean, under Apache 2.0.
Modifications: specialize to the canonical complex-point space of a scheme;
add a pointwise normalized regular-function map and module pullback.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.AlgebraicGeometry.ComplexAnalytification

/-!
# A normalized analytic realization of a complex scheme

The carrier and topology are the actual complex points of the scheme. The
analytic structure is a complex manifold structure on that carrier, and its
structure sheaf consists of complex-smooth, hence holomorphic, functions.
The map from regular functions is fixed by evaluation at every complex point.

`AnalyticManifold` and `RegularFunctions` are characterized input data. This
file constructs their ringed-space and module functors; it does not assert
that every smooth complex scheme has such data.
-/

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open scoped Manifold ContDiff

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticRealization

open MathlibExt.AlgebraicGeometry.ComplexAnalytification

/-- Complex schemes with their specified map to `Spec ℂ`. -/
abbrev ComplexScheme := Over (Spec (CommRingCat.of.{0} ℂ))

/-- The finite-dimensional complex coordinate model. -/
abbrev CoordinateSpace (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- The scheme point underlying a complex point, as a continuous map. -/
def pointMap (X : ComplexScheme) : space X ⟶ X.left.toRingedSpace.carrier :=
  TopCat.ofHom
    ⟨ComplexPoints.schemePoint, by
      rw [continuous_def]
      intro U hU
      let V : X.left.Opens := ⟨U, hU⟩
      convert ComplexPoints.isOpen_setOf_mem (y := X.hom) V using 1
      ext p
      exact ComplexPoints.schemePoint_mem_iff p V⟩

/-- A complex manifold structure on the fixed complex-point topology. -/
class AnalyticManifold (X : ComplexScheme) (d : ℕ) where
  /-- Coordinate charts on the actual complex points. -/
  chartedSpace : ChartedSpace (CoordinateSpace d) (space X)
  /-- The charts have holomorphic transition maps. -/
  isManifold : @IsManifold ℂ _ (CoordinateSpace d) _ _
    (CoordinateSpace d) _ 𝓘(ℂ, CoordinateSpace d) ∞ (space X) _ chartedSpace

attribute [instance, instance_reducible] AnalyticManifold.chartedSpace
attribute [instance] AnalyticManifold.isManifold

variable (X : ComplexScheme) (d : ℕ) [AnalyticManifold X d]

/-- Holomorphic functions on the specified complex manifold. -/
noncomputable abbrev holomorphicSheaf :
    TopCat.Sheaf CommRingCat (space X) :=
  smoothSheafCommRing 𝓘(ℂ, CoordinateSpace d) 𝓘(ℂ) (space X) ℂ

/-- The holomorphic structure sheaf, considered as a sheaf of rings. -/
noncomputable abbrev holomorphicRingSheaf :
    TopCat.Sheaf RingCat (space X) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat)).obj
    (holomorphicSheaf X d)

/-- Analytic inverse image of an algebraic open set. -/
def analyticOpen (U : X.left.Opens) : Opens (space X) :=
  (Opens.map (pointMap X)).obj U

/-- The analytic structure map sends every regular function to its actual
complex-point evaluation. Its ring and restriction laws are those of the
natural transformation; the normalization excludes a free map of rings. -/
class RegularFunctions where
  /-- Pull regular functions back to holomorphic functions. -/
  regularMap : X.left.presheaf ⟶
    (TopCat.Presheaf.pushforward CommRingCat (pointMap X)).obj
      (holomorphicSheaf X d).obj
  /-- The analytic function is precisely regular-function evaluation. -/
  regularMap_eval (U : X.left.Opens) (g : Γ(X.left, U))
      (p : analyticOpen X U) :
    (show C^∞⟮𝓘(ℂ, CoordinateSpace d), analyticOpen X U; 𝓘(ℂ), ℂ⟯
      from regularMap.app (op U) g) p =
      ComplexPoints.eval g p.1
        ((ComplexPoints.schemePoint_mem_iff p.1 U).mp p.2)

variable [RegularFunctions X d]

/-- The actual holomorphic ringed space of the specified realization. -/
noncomputable def ringedSpace : RingedSpace where
  carrier := space X
  presheaf := (holomorphicSheaf X d).obj
  IsSheaf := (holomorphicSheaf X d).property

/-- The pointwise normalized analytic-to-algebraic map of ringed spaces. -/
noncomputable def ringedMap : ringedSpace X d ⟶ X.left.toRingedSpace :=
  InducedCategory.homMk
    { base := pointMap X
      c := RegularFunctions.regularMap }

/-- The structure map on underlying sheaves of rings. -/
noncomputable def ringMap : X.left.ringCatSheaf ⟶
    ((Opens.map (pointMap X)).sheafPushforwardContinuous _ _ _).obj
      (holomorphicRingSheaf X d) where
  hom := Functor.whiskerRight RegularFunctions.regularMap
    (forget₂ CommRingCat RingCat)

/-- Sheaves of modules over the actual holomorphic structure sheaf. -/
abbrev AnalyticModules := SheafOfModules.{0} (holomorphicRingSheaf X d)

/-- The existing presheaf pullback constructor applies to these small sites. -/
instance presheafPushforward_isRightAdjoint :
    (PresheafOfModules.pushforward.{0} (F := Opens.map (pointMap X))
      (ringMap X d).hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top
      (F := Opens.map (pointMap X)) (ringMap X d).hom)

/-- The sheaf pullback is supplied by the actual sheafification adjunction. -/
instance sheafPushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{0} (F := Opens.map (pointMap X))
      (ringMap X d)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{0}
    (F := Opens.map (pointMap X)) (ringMap X d)).isRightAdjoint

/-- The actual pullback of algebraic modules to holomorphic modules. -/
noncomputable def pullback : X.left.Modules ⥤ AnalyticModules X d :=
  SheafOfModules.pullback.{0} (F := Opens.map (pointMap X)) (ringMap X d)

/-- The actual pushforward of holomorphic modules to algebraic modules. -/
noncomputable def pushforward : AnalyticModules X d ⥤ X.left.Modules :=
  SheafOfModules.pushforward.{0} (F := Opens.map (pointMap X)) (ringMap X d)

/-- The analytic module functors have their defining adjunction. -/
noncomputable def pullbackPushforwardAdjunction :
    pullback X d ⊣ pushforward X d :=
  SheafOfModules.pullbackPushforwardAdjunction.{0}
    (F := Opens.map (pointMap X)) (ringMap X d)

end MathlibExt.AlgebraicGeometry.AnalyticRealization
