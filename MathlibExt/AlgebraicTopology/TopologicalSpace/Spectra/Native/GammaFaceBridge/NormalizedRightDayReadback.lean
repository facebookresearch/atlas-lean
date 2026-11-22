/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.CanonicalCastRightDayReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.SourceDayContext
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.SourceDiagramPair
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalDiagramPair
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.NativeTypes
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NativeCanonicalPairCast

/-!
# Normalized Right Day Readback

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
open NativeModuleEvaluation
section Selected
universe uV vV uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ]
  [HasColimitsOfSize.{0, 0} V] [HasProducts.{0} V] [HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V ℕ)
  {J : Type uJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

open CommutativeModuleConversion

/-- The whole original q/c source right word after its actual identity tensor comparison,
retaining the original source adjuncts, unit transport, Day point, action and counit. -/
def NormalizedRightDayReadback (M : MonoidalCategory (EnrichedFunctorCat V J))
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
    (f : Free.object (c.indexMap n) K ⟶ N)
    (g : Free.object (c.indexMap r) L ⟶ 𝟙_ (EnrichedFunctorCat V J)),
    Free.evaluate (c.indexMap (q.monoidalData.tensorEnrichedFunctor.obj (n, r))) (K ⊗ L) N
      ((p n r K L).inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom) =
    (((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction q.coefficient n).homEquiv
        K (c.sourceEquivalence.inverse.obj N)
        (sourcePreimage q.coefficient c.sourceEquivalence c.indexMap c.evaluationComparison n K N f) ⊗ₘ
      (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction q.coefficient r).homEquiv
        L (𝟙_ (RightModule q.coefficient))
        (sourcePreimage q.coefficient c.sourceEquivalence c.indexMap c.evaluationComparison r L
          (c.sourceEquivalence.functor.obj (𝟙_ (RightModule q.coefficient)))
          (g ≫ eqToHom (congrArg (fun Z : MonoidalCategory (EnrichedFunctorCat V J) =>
            Z.tensorUnit) hM.symm)) ≫
          c.sourceEquivalence.unitIso.inv.app (𝟙_ (RightModule q.coefficient)))) ≫
      EnrichedDayKernel.Generators.point q.monoidalData.tensorEnrichedFunctor
        (c.sourceEquivalence.inverse.obj N).X.toEnrichedFunctor q.coefficient.toEnrichedFunctor (n, r) ≫
      component (c.sourceEquivalence.inverse.obj N).action (q.monoidalData.tensorEnrichedFunctor.obj (n, r))) ≫
      (c.evaluationComparison (q.monoidalData.tensorEnrichedFunctor.obj (n, r))).inv.app
        (c.sourceEquivalence.inverse.obj N) ≫
      component (c.sourceEquivalence.counitIso.hom.app N)
        (c.indexMap (q.monoidalData.tensorEnrichedFunctor.obj (n, r)))

/-- Eliminate the original identity tensor comparison while all original source instances
are abstract q/c fields, before instantiating any native coefficient object. -/
theorem selected_right_day_readback_drop_comparison
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M)
    (p : Independent.PairFormula M (fun n K => Free.object (c.indexMap n) K)
      (fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r)))
    (hRead : SelectedCastRightDayReadback q c q.monoidalData.tensorEnrichedFunctor
      (DayTensorBridge.originalTensorComparison q.monoidalData) M hM p) :
    NormalizedRightDayReadback q c M hM p := by
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
    (c.sourceEquivalence.inverse.obj N).X q.coefficient).2
  have hId := Category.id_comp (c.sourceEquivalence.inverse.obj N).action
  simp only [hTC, hId] at h0
  exact h0

end Selected
end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
