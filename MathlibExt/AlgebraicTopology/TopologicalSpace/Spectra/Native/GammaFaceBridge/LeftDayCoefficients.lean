/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NormalizedLeftWord
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.UnitPreimageEvaluation

/-!
# Left Day Coefficients

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Limits
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
open NativeModuleEvaluation CommutativeModuleConversion
universe uV vV uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ]
  [HasColimitsOfSize.{0, 0} V] [HasProducts.{0} V] [HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V ℕ)
  {J : Type uJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- The original first source adjunction coefficient, with its full unit-target cast. -/
def LeftDayUnitCoefficient (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M) :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI : MonoidalCategory (RightModule q.coefficient) := RightModuleFree.tensorMonoidal q.coefficient
  letI := M
  fun (n : ℕ) (K : V)
    (f : Free.object (c.indexMap n) K ⟶ 𝟙_ (EnrichedFunctorCat V J)) =>
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction q.coefficient n).homEquiv
      K (𝟙_ (RightModule q.coefficient))
      (sourcePreimage q.coefficient c.sourceEquivalence c.indexMap c.evaluationComparison n K
        (c.sourceEquivalence.functor.obj (𝟙_ (RightModule q.coefficient)))
        (f ≫ eqToHom (congrArg (fun Z : MonoidalCategory (EnrichedFunctorCat V J) =>
          Z.tensorUnit) hM.symm)) ≫
        c.sourceEquivalence.unitIso.inv.app (𝟙_ (RightModule q.coefficient)))

/-- The original second source adjunction coefficient for every entire native free map. -/
def LeftDayMapCoefficient :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI : MonoidalCategory (RightModule q.coefficient) := RightModuleFree.tensorMonoidal q.coefficient
  fun (r : ℕ) (L : V) (N : EnrichedFunctorCat V J)
    (g : Free.object (c.indexMap r) L ⟶ N) =>
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction q.coefficient r).homEquiv
      L (c.sourceEquivalence.inverse.obj N)
      (sourcePreimage q.coefficient c.sourceEquivalence c.indexMap c.evaluationComparison r L N g)

/-- Factoring a source word at its exact two source coefficients introduces no new maps. -/
theorem normalized_left_day_word_coefficients
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M) :
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI : MonoidalCategory (RightModule q.coefficient) := RightModuleFree.tensorMonoidal q.coefficient
  letI := M
  ∀ (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (c.indexMap n) K ⟶ 𝟙_ (EnrichedFunctorCat V J))
    (g : Free.object (c.indexMap r) L ⟶ N),
    NormalizedLeftDayWord q c M hM n r K L N f g =
    (((LeftDayUnitCoefficient q c M hM n K f ⊗ₘ LeftDayMapCoefficient q c r L N g) ≫
      EnrichedDayKernel.Generators.point q.monoidalData.tensorEnrichedFunctor
        q.coefficient.toEnrichedFunctor (c.sourceEquivalence.inverse.obj N).X.toEnrichedFunctor (n, r) ≫
      component (leftAction q.coefficient (c.sourceEquivalence.inverse.obj N))
        (q.monoidalData.tensorEnrichedFunctor.obj (n, r))) ≫
      (c.evaluationComparison (q.monoidalData.tensorEnrichedFunctor.obj (n, r))).inv.app
        (c.sourceEquivalence.inverse.obj N) ≫
      component (c.sourceEquivalence.counitIso.hom.app N)
        (c.indexMap (q.monoidalData.tensorEnrichedFunctor.obj (n, r)))) := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let : MonoidalCategory (RightModule q.coefficient) := RightModuleFree.tensorMonoidal q.coefficient
  let := M
  intro n r K L N f g
  rfl

/-- The second original coefficient retains its exact comparison and source counit. -/
theorem left_day_map_coefficient_evaluate :
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI : MonoidalCategory (RightModule q.coefficient) := RightModuleFree.tensorMonoidal q.coefficient
  ∀ (r : ℕ) (L : V) (N : EnrichedFunctorCat V J)
    (g : Free.object (c.indexMap r) L ⟶ N),
    LeftDayMapCoefficient q c r L N g ≫
      (c.evaluationComparison r).inv.app (c.sourceEquivalence.inverse.obj N) ≫
      component (c.sourceEquivalence.counitIso.hom.app N) (c.indexMap r) =
    Free.evaluate (c.indexMap r) L N g := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let : MonoidalCategory (RightModule q.coefficient) := RightModuleFree.tensorMonoidal q.coefficient
  intro r L N g
  exact sourcePreimage_evaluate q.coefficient c.sourceEquivalence c.indexMap
    c.evaluationComparison r L N g


omit [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ] [HasColimitsOfSize.{0, 0} V]
  [HasProducts.{0} V] [HasEqualizers V] in
/-- Evaluation of the original target-unit equality is its exact equality on level spaces. -/
theorem source_unit_cast_component {F G : EnrichedFunctorCat V J} (e : F = G) (j : J) :
    component (eqToHom e) j =
      eqToHom (congrArg (fun Z : EnrichedFunctorCat V J => Z.toEnrichedFunctor.obj j) e) := by
  cases e
  simp only [eqToHom_refl, component_id]

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
