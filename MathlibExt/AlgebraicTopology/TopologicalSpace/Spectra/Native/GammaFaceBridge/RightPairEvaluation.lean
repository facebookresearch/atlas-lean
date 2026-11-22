/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.RightDayComposition

/-!
# Right Pair Evaluation

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

/-- The full right pair word evaluated on its original free coefficient. All pair
objects, coefficient maps, native tensor maps and the right unitor remain explicit. -/
def RightPairEvaluationWord
    (M : MonoidalCategory (EnrichedFunctorCat V J)) (a : ℕ → J) (t : ℕ → ℕ → ℕ)
    (p : Independent.PairFormula M (fun n K => Free.object (a n) K) t) :=
  letI := M
  fun (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (a n) K ⟶ N)
    (g : Free.object (a r) L ⟶ 𝟙_ (EnrichedFunctorCat V J)) =>
    Free.evaluate (a (t n r)) (K ⊗ L) N
      ((p n r K L).inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom)
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

/-- Read the complete original right family into its named evaluated arrow before
specializing any selected source labels or module dictionaries. -/
theorem normalized_right_day_readback_evaluation_word
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : primitiveMonoidal q c = M)
    (p : Independent.PairFormula M (fun n K => Free.object (c.indexMap n) K)
      (fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r)))
    (hRead : NormalizedRightDayReadback q c M hM p) :
    letI := M
    ∀ (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
      (f : Free.object (c.indexMap n) K ⟶ N)
      (g : Free.object (c.indexMap r) L ⟶ 𝟙_ (EnrichedFunctorCat V J)),
      RightPairEvaluationWord M c.indexMap
        (fun n r => q.monoidalData.tensorEnrichedFunctor.obj (n, r)) p n r K L N f g =
      NormalizedRightDayWord q c M hM n r K L N f g := by
  exact hRead
end Selected
end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
