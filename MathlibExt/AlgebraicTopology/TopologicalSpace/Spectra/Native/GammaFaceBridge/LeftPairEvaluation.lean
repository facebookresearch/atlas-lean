/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.NormalizedLeftWord

/-!
# Left Pair Evaluation

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
universe uV vV uJ
section Evaluation
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] {J : Type uJ} [EnrichedCategory V J]

/-- The complete original evaluated left pair word, retaining both free maps,
the full pair inverse, original tensor map and original left unitor. -/
def LeftPairEvaluationWord
    (M : MonoidalCategory (EnrichedFunctorCat V J)) (a : ℕ → J) (t : ℕ → ℕ → ℕ)
    (p : Independent.PairFormula M (fun n K => Free.object (a n) K) t) :=
  letI := M
  fun (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (a n) K ⟶ 𝟙_ (EnrichedFunctorCat V J))
    (g : Free.object (a r) L ⟶ N) =>
    Free.evaluate (a (t n r)) (K ⊗ L) N
      ((p n r K L).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom)

/-- The named evaluated word is exactly the original full evaluated arrow at
every source index and coefficient map, before specializing the pair family. -/
theorem left_pair_evaluation_word_formula
    (M : MonoidalCategory (EnrichedFunctorCat V J)) (a : ℕ → J) (t : ℕ → ℕ → ℕ)
    (p : Independent.PairFormula M (fun n K => Free.object (a n) K) t) :
    letI := M
    ∀ (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
      (f : Free.object (a n) K ⟶ 𝟙_ (EnrichedFunctorCat V J))
      (g : Free.object (a r) L ⟶ N),
      LeftPairEvaluationWord M a t p n r K L N f g =
      Free.evaluate (a (t n r)) (K ⊗ L) N
        ((p n r K L).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom) := by
  exact fun _ _ _ _ _ _ _ => rfl
end Evaluation

section Selected
open NativeModuleEvaluation CommutativeModuleConversion
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ]
  [HasColimitsOfSize.{0, 0} V] [HasProducts.{0} V] [HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V ℕ)
  {J : Type uJ} [EnrichedCategory V J]
  (c : CanonicalSourceFreeSmash.SelectedPair.Context q J)

/-- The entire original selected left readback identifies its named evaluated
arrow with the complete original source Day word and unit-target cast. -/
theorem normalized_left_day_readback_evaluation_word
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M)
    (p : Independent.PairFormula M (fun n K => Free.object (c.indexMap n) K)
      (fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r)))
    (hRead : NormalizedLeftDayReadback q c M hM p) :
    letI := M
    ∀ (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
      (f : Free.object (c.indexMap n) K ⟶ 𝟙_ (EnrichedFunctorCat V J))
      (g : Free.object (c.indexMap r) L ⟶ N),
      LeftPairEvaluationWord M c.indexMap
        (fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r)) p n r K L N f g =
      NormalizedLeftDayWord q c M hM n r K L N f g := by
  exact hRead
end Selected
end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
