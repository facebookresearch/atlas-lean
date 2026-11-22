/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.ModulePairEvaluation

/-!
# Unit Preimage Evaluation

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe uV vV uI uJ
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeModuleEvaluation
open PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash
open CommutativeModuleConversion
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S]
  {J : Type uJ} [EnrichedCategory V J]
  (E : RightModule S ≌ EnrichedFunctorCat V J) (a : I → J)
  (h : ∀ n, E.functor ⋙ evaluation (a n) ≅
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)
  (M : MonoidalCategory (RightModule S))

/-- The original unit-target preimage keeps the actual inverse equivalence unit. -/
def unitPreimage (n : I) (K : V) :
    letI := M
    letI := Monoidal.transport E
    (Free.object (a n) K ⟶ 𝟙_ (EnrichedFunctorCat V J)) →
      ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj K ⟶
        𝟙_ (RightModule S)) := by
  letI := M
  letI := Monoidal.transport E
  intro f
  exact sourcePreimage S E a h n K (𝟙_ (EnrichedFunctorCat V J)) f ≫
    E.unitIso.inv.app (𝟙_ (RightModule S))

/-- Applying `E` to a unit-target source preimage and the inverse free comparison reconstructs the
native free map. -/
def UnitReconstructFormula (n : I) (K : V) : Prop :=
  letI := M
  letI := Monoidal.transport E
  ∀ (f : Free.object (a n) K ⟶ 𝟙_ (EnrichedFunctorCat V J)),
    (ModuleStage.sourceComparison S E a h n).inv.app K ≫
      E.functor.map (unitPreimage S E a h M n K f) = f

/-- Every entire native unit-target free map is the image of its original source preimage. -/
theorem unit_preimage_reconstruct (n : I) (K : V) :
    UnitReconstructFormula S E a h M n K := by
  let := M
  let := Monoidal.transport E
  intro f
  have hu := E.counit_app_functor (𝟙_ (RightModule S))
  change E.counitIso.hom.app (𝟙_ (EnrichedFunctorCat V J)) =
    E.functor.map (E.unitIso.inv.app (𝟙_ (RightModule S))) at hu
  rw [unitPreimage, E.functor.map_comp, ← hu]
  exact sourcePreimage_reconstruct S E a h n K (𝟙_ (EnrichedFunctorCat V J)) f

/-- The source free adjunction evaluates a unit-target preimage to the same coefficient as native
free evaluation. -/
def UnitEvaluationFormula (n : I) (K : V) : Prop :=
  letI := M
  letI := Monoidal.transport E
  ∀ (f : Free.object (a n) K ⟶ 𝟙_ (EnrichedFunctorCat V J)),
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv
      K (𝟙_ (RightModule S)) (unitPreimage S E a h M n K f) ≫
        (h n).inv.app (𝟙_ (RightModule S)) =
      Free.evaluate (a n) K (𝟙_ (EnrichedFunctorCat V J)) f

/-- The original source unit-target adjunction reads the unchanged entire native coefficient. -/
theorem unit_preimage_evaluate (n : I) (K : V) :
    UnitEvaluationFormula S E a h M n K := by
  let := M
  let := Monoidal.transport E
  intro f
  have hp := FreeAdjunctionSource.point E (a n)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n) (h n)
    (unitPreimage S E a h M n K f)
  change (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv
      K (𝟙_ (RightModule S)) (unitPreimage S E a h M n K f) ≫
        (h n).inv.app (𝟙_ (RightModule S)) =
    Free.evaluate (a n) K (𝟙_ (EnrichedFunctorCat V J))
      ((ModuleStage.sourceComparison S E a h n).inv.app K ≫
        E.functor.map (unitPreimage S E a h M n K f)) at hp
  rw [unit_preimage_reconstruct S E a h M n K f] at hp
  exact hp

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeModuleEvaluation
