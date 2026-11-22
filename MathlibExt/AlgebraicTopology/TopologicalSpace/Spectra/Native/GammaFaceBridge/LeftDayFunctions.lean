/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.LeftDayCoefficients
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.UnitPreimageEvaluation

/-!
# Left Day Functions

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

/-- The complete original left Day point followed by the original module action. -/
def LeftDayAction :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI : MonoidalCategory (RightModule q.coefficient) := RightModuleFree.tensorMonoidal q.coefficient
  fun (n r : ℕ) (N : EnrichedFunctorCat V J) =>
    EnrichedDayKernel.Generators.point q.monoidalData.tensorEnrichedFunctor
      q.coefficient.toEnrichedFunctor (c.sourceEquivalence.inverse.obj N).X.toEnrichedFunctor (n, r) ≫
    component (leftAction q.coefficient (c.sourceEquivalence.inverse.obj N))
      (q.monoidalData.tensorEnrichedFunctor.obj (n, r))

/-- The unchanged evaluation comparison followed by the complete original source counit. -/
def LeftDayTargetTail :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI : MonoidalCategory (RightModule q.coefficient) := RightModuleFree.tensorMonoidal q.coefficient
  fun (s : ℕ) (N : EnrichedFunctorCat V J) =>
    (c.evaluationComparison s).inv.app (c.sourceEquivalence.inverse.obj N) ≫
    component (c.sourceEquivalence.counitIso.hom.app N) (c.indexMap s)

/-- The original word factors into its two exact coefficients, action and target tail. -/
theorem normalized_left_day_word_factors
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
    (LeftDayUnitCoefficient q c M hM n K f ⊗ₘ LeftDayMapCoefficient q c r L N g) ≫
      LeftDayAction q c n r N ≫
      LeftDayTargetTail q c (q.monoidalData.tensorEnrichedFunctor.obj (n, r)) N := by
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
  simp only [NormalizedLeftDayWord, LeftDayUnitCoefficient, LeftDayMapCoefficient,
    LeftDayAction, LeftDayTargetTail, Category.assoc]

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
