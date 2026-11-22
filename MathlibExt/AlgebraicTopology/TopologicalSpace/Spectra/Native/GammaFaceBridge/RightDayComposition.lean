/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.RightWordCoefficients

/-!
# Right Day Composition

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

/-- The complete original right Day point followed by the original module action.
The source module and all its implicit dictionaries are retained in this boundary. -/
def RightDaySourceAction :=
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
      (c.sourceEquivalence.inverse.obj N).X.toEnrichedFunctor q.coefficient.toEnrichedFunctor (n, r) ≫
    component (c.sourceEquivalence.inverse.obj N).action
      (q.monoidalData.tensorEnrichedFunctor.obj (n, r))

/-- The complete original target inverse comparison and source counit. -/
def RightDayTargetTail :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI : MonoidalCategory (RightModule q.coefficient) := RightModuleFree.tensorMonoidal q.coefficient
  fun (n r : ℕ) (N : EnrichedFunctorCat V J) =>
    (c.evaluationComparison (q.monoidalData.tensorEnrichedFunctor.obj (n, r))).inv.app
      (c.sourceEquivalence.inverse.obj N) ≫
    component (c.sourceEquivalence.counitIso.hom.app N)
      (c.indexMap (q.monoidalData.tensorEnrichedFunctor.obj (n, r)))

/-- Factor the entire original right word at ordinary action and tail boundaries
before specializing any source provider or coefficient. -/
theorem normalized_right_day_word_composition
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
    (f : Free.object (c.indexMap n) K ⟶ N)
    (g : Free.object (c.indexMap r) L ⟶ 𝟙_ (EnrichedFunctorCat V J)),
    NormalizedRightDayWord q c M hM n r K L N f g =
      ((LeftDayMapCoefficient q c n K N f ⊗ₘ LeftDayUnitCoefficient q c M hM r L g) ≫
        RightDaySourceAction q c n r N) ≫ RightDayTargetTail q c n r N := by
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

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
