/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.LeftDayCoefficients
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.UnitPreimageEvaluation

/-!
# Left Day Unit Readback

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

/-- The first original coefficient reads through its original unit comparison before
any target-unit cast is normalized. -/
theorem left_day_unit_coefficient_evaluate
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
  ∀ (n : ℕ) (K : V)
    (f : Free.object (c.indexMap n) K ⟶ 𝟙_ (EnrichedFunctorCat V J)),
    LeftDayUnitCoefficient q c M hM n K f ≫
      (c.evaluationComparison n).inv.app (𝟙_ (RightModule q.coefficient)) =
    Free.evaluate (c.indexMap n) K
      (c.sourceEquivalence.functor.obj (𝟙_ (RightModule q.coefficient)))
      (f ≫ eqToHom (congrArg (fun Z : MonoidalCategory (EnrichedFunctorCat V J) =>
        Z.tensorUnit) hM.symm)) := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let : MonoidalCategory (RightModule q.coefficient) := RightModuleFree.tensorMonoidal q.coefficient
  let := M
  intro n K f
  cases hM
  have hp := unit_preimage_evaluate (V := V) (I := ℕ) (J := J)
    q.coefficient c.sourceEquivalence c.indexMap c.evaluationComparison
    (RightModuleFree.tensorMonoidal q.coefficient) n K f
  convert hp using 1 <;>
    simp only [LeftDayUnitCoefficient, unitPreimage, sourcePreimage,
      Free.evaluate, component, eqToHom_refl, Category.comp_id]
  all_goals rfl

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
