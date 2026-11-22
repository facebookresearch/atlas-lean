/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.CanonicalNormalizedRightDay

/-!
# Normalized Right Word

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
section Selected
universe uV vV uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ]
  [HasColimitsOfSize.{0, 0} V] [HasProducts.{0} V] [HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V ℕ)
  {J : Type uJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- The complete source right word keeps both original adjunctions, the source unit
transport, original Day generator and action, and target comparison and counit. -/
def NormalizedRightDayWord (M : MonoidalCategory (EnrichedFunctorCat V J))
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
  fun (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (c.indexMap n) K ⟶ N)
    (g : Free.object (c.indexMap r) L ⟶ 𝟙_ (EnrichedFunctorCat V J)) =>
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

/-- Read a pair into its entire named source word before specializing the original
source data or any coefficient map. -/
theorem normalized_right_day_readback_word
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M)
    (p : Independent.PairFormula M (fun n K => Free.object (c.indexMap n) K)
      (fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r)))
    (hRead : NormalizedRightDayReadback q c M hM p) :
    letI := M
    ∀ (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
      (f : Free.object (c.indexMap n) K ⟶ N)
      (g : Free.object (c.indexMap r) L ⟶ 𝟙_ (EnrichedFunctorCat V J)),
      Free.evaluate (c.indexMap (q.monoidalData.tensorEnrichedFunctor.obj (n, r))) (K ⊗ L) N
        ((p n r K L).inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom) =
      NormalizedRightDayWord q c M hM n r K L N f g := by
  exact hRead

end Selected
end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
