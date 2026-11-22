/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.CanonicalCastLeftDayReadback

/-!
# Normalized Left Day Readback

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

/-- The original left source Day word after its identity tensor comparison, retaining both
source preimages, the source-unit cast, original Day point, left action and target counit. -/
def NormalizedLeftDayReadback (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M)
    (p : Independent.PairFormula M (fun n K => Free.object (c.indexMap n) K)
      (fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r))) : Prop :=
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
    Free.evaluate (c.indexMap (q.monoidalData.tensorEnrichedFunctor.obj (n, r))) (K ⊗ L) N
      ((p n r K L).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom) =
    (((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction q.coefficient n).homEquiv
        K (𝟙_ (RightModule q.coefficient))
        (sourcePreimage q.coefficient c.sourceEquivalence c.indexMap c.evaluationComparison n K
          (c.sourceEquivalence.functor.obj (𝟙_ (RightModule q.coefficient)))
          (f ≫ eqToHom (congrArg (fun Z : MonoidalCategory (EnrichedFunctorCat V J) =>
            Z.tensorUnit) hM.symm)) ≫
          c.sourceEquivalence.unitIso.inv.app (𝟙_ (RightModule q.coefficient))) ⊗ₘ
      (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction q.coefficient r).homEquiv
        L (c.sourceEquivalence.inverse.obj N)
        (sourcePreimage q.coefficient c.sourceEquivalence c.indexMap c.evaluationComparison r L N g)) ≫
      EnrichedDayKernel.Generators.point q.monoidalData.tensorEnrichedFunctor
        q.coefficient.toEnrichedFunctor (c.sourceEquivalence.inverse.obj N).X.toEnrichedFunctor (n, r) ≫
      component (leftAction q.coefficient (c.sourceEquivalence.inverse.obj N))
        (q.monoidalData.tensorEnrichedFunctor.obj (n, r))) ≫
      (c.evaluationComparison (q.monoidalData.tensorEnrichedFunctor.obj (n, r))).inv.app
        (c.sourceEquivalence.inverse.obj N) ≫
      component (c.sourceEquivalence.counitIso.hom.app N)
        (c.indexMap (q.monoidalData.tensorEnrichedFunctor.obj (n, r)))

/-- Remove the original identity comparison while all source instances are still abstract
selected fields, before specializing any native coefficient or module object. -/
theorem selected_left_day_readback_drop_comparison
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M)
    (p : Independent.PairFormula M (fun n K => Free.object (c.indexMap n) K)
      (fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r)))
    (hRead : SelectedCastLeftDayReadback q c q.monoidalData.tensorEnrichedFunctor
      (DayTensorBridge.originalTensorComparison q.monoidalData) M hM p) :
    NormalizedLeftDayReadback q c M hM p := by
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
  have h0 := hRead n r K L N f g
  have hTC := (DayTensorBridge.originalTensorComparison_components q.monoidalData
    q.coefficient (c.sourceEquivalence.inverse.obj N).X).2
  have hId := Category.id_comp (leftAction q.coefficient (c.sourceEquivalence.inverse.obj N))
  simp only [hTC, hId] at h0
  exact h0

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
