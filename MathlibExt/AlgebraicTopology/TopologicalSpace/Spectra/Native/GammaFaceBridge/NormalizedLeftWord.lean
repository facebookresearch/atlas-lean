/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.CanonicalNormalizedLeftDay

/-!
# Normalized Left Word

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

/-- The complete original source left word, named before any native pair is specialized. -/
def NormalizedLeftDayWord (M : MonoidalCategory (EnrichedFunctorCat V J))
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
    (f : Free.object (c.indexMap n) K ⟶ 𝟙_ (EnrichedFunctorCat V J))
    (g : Free.object (c.indexMap r) L ⟶ N) =>
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

/-- Read the cast family into a named source word while the selected source is abstract. -/
theorem named_left_day_readback
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M)
    (p : Independent.PairFormula M (fun n K => Free.object (c.indexMap n) K)
      (fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r)))
    (hRead : NormalizedLeftDayReadback q c M hM p) :
    letI := M
    ∀ (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
      (f : Free.object (c.indexMap n) K ⟶ 𝟙_ (EnrichedFunctorCat V J))
      (g : Free.object (c.indexMap r) L ⟶ N),
      Free.evaluate (c.indexMap (q.monoidalData.tensorEnrichedFunctor.obj (n, r))) (K ⊗ L) N
        ((p n r K L).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom) =
      NormalizedLeftDayWord q c M hM n r K L N f g := by
  exact hRead

/-- Apply the original canonical cast and identity comparison before naming the source word. -/
theorem cast_canonical_left_day_word_evaluate
    (ht : c.tensorIndex = fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r))
    (he : letI := q.dayMonoidal
      cast (congrArg (SourceDiagramFamilyType q) ht) c.diagramPair =
        (fun n r K L => (DayTensorBridge.originalTensorComparison q.monoidalData).app
          (Free.object n K, Free.object r L) ≪≫
          EnrichedDayKernel.FreePairComparison.iso q.monoidalData.tensorEnrichedFunctor n r K L))
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M)
    (hType : CanonicalSourceFreeSmash.SelectedPair.PairIsoType c =
      Independent.PairFormula M (fun n K => Free.object (c.indexMap n) K)
        (fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r))) :
    letI := M
    ∀ (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
      (f : Free.object (c.indexMap n) K ⟶ 𝟙_ (EnrichedFunctorCat V J))
      (g : Free.object (c.indexMap r) L ⟶ N),
      Free.evaluate (c.indexMap (q.monoidalData.tensorEnrichedFunctor.obj (n, r))) (K ⊗ L) N
        (((cast hType (CanonicalSourceFreeSmash.SelectedPair.pairIso c)) n r K L).inv ≫
          (f ⊗ₘ g) ≫ (λ_ N).hom) =
      NormalizedLeftDayWord q c M hM n r K L N f g :=
  named_left_day_readback q c M hM
    (cast hType (CanonicalSourceFreeSmash.SelectedPair.pairIso c))
    (cast_canonical_normalized_left_day_readback q c ht he M hM hType)

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
