/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.InitialSquareHC
import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteLatchingFromOriginalAllOperators
import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalTensorHC

/-!
# Incoming comparisons for finite degeneracy source overlaps

Sharp row maps and weak relative comparisons for every simplex operator imply that each finite degeneracy source-overlap square is homotopy cartesian. The weak comparison uses the full source-overlap map and its inclusion into the row in every degree and at every finite stage.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkSourceOverlapIncoming
open SharpComparisonDraft RezkCompatiblePushout RezkSkeletalProduct

/-- The ACTUAL source of each degeneracy overlap is HC into the preceding
row, from original row Sharp and ALL operator comparisons. The zero face
is retained as the genuine empty initial square. -/
theorem source_overlap_row_hc {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f)) :
    ∀ (n : ℕ) (r : Fin (n + 1)), WeakEquivalence
      (pullback.lift (outerLatchingStageSourceOverlap X n r).ι
        (outerLatchingStageSourceOverlapMap eta n r)
        (outerLatchingStageSourceOverlapMap_ι eta n r).symm ≫
        comparison (eta.app (op ⦋n⦌)) (outerLatchingStageSourceOverlap Y n r).ι) := by
  intro n r
  cases n with
  | zero =>
      have hr : r = 0 := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ r.isLt)
      subst r
      have initX : IsInitial (outerLatchingStageSourceOverlap X 0 0 : SSet.{u}) := by
        rw [outerLatchingStageSourceOverlap_zero]
        exact Subcomplex.isInitialBot (X := _)
      have initY : IsInitial (outerLatchingStageSourceOverlap Y 0 0 : SSet.{u}) := by
        rw [outerLatchingStageSourceOverlap_zero]
        exact Subcomplex.isInitialBot (X := _)
      exact RezkEmptyFace.initialSquare_hc initX initY
        (outerLatchingStageSourceOverlap X 0 0).ι (outerLatchingStageSourceOverlapMap eta 0 0)
        (eta.app (op ⦋0⦌)) (outerLatchingStageSourceOverlap Y 0 0).ι (hrows ⦋0⦌)
  | succ n =>
      induction r using Fin.cases with
      | zero =>
          have initX : IsInitial (outerLatchingStageSourceOverlap X (n + 1) 0 : SSet.{u}) := by
            rw [outerLatchingStageSourceOverlap_zero]
            exact Subcomplex.isInitialBot (X := _)
          have initY : IsInitial (outerLatchingStageSourceOverlap Y (n + 1) 0 : SSet.{u}) := by
            rw [outerLatchingStageSourceOverlap_zero]
            exact Subcomplex.isInitialBot (X := _)
          exact RezkEmptyFace.initialSquare_hc initX initY
            (outerLatchingStageSourceOverlap X (n + 1) 0).ι
                (outerLatchingStageSourceOverlapMap eta (n + 1) 0)
            (eta.app (op ⦋n + 1⦌)) (outerLatchingStageSourceOverlap Y (n + 1) 0).ι (hrows ⦋n + 1⦌)
      | succ r =>
          let eX : (outerLatchingStageSourceOverlap X (n + 1) r.succ : SSet.{u}) ≅
              outerLatchingStage X n r :=
            Subcomplex.eqToIso (outerLatchingStageSourceOverlap_succ X n r)
          let eY : (outerLatchingStageSourceOverlap Y (n + 1) r.succ : SSet.{u}) ≅
              outerLatchingStage Y n r :=
            Subcomplex.eqToIso (outerLatchingStageSourceOverlap_succ Y n r)
          have ex : eX.hom ≫ (outerLatchingStage X n r).ι =
              (outerLatchingStageSourceOverlap X (n + 1) r.succ).ι := by
            simp [eX, Subcomplex.eqToIso]
          have ey : eY.hom ≫ (outerLatchingStage Y n r).ι =
              (outerLatchingStageSourceOverlap Y (n + 1) r.succ).ι := by
            simp [eY, Subcomplex.eqToIso]
          have over : eX.hom ≫ outerLatchingStageMap eta n r =
              outerLatchingStageSourceOverlapMap eta (n + 1) r.succ ≫ eY.hom := by
            apply (cancel_mono (outerLatchingStage Y n r).ι).mp
            simp only [Category.assoc, outerLatchingStageMap_ι, ey,
              outerLatchingStageSourceOverlapMap_ι]
            rw [← Category.assoc, ex]
          let old : CommSq (outerLatchingStageSourceOverlap X (n + 1) r.succ).ι
              (outerLatchingStageSourceOverlapMap eta (n + 1) r.succ)
              (eta.app (op ⦋n + 1⦌)) (outerLatchingStageSourceOverlap Y (n + 1) r.succ).ι :=
            CommSq.mk (outerLatchingStageSourceOverlapMap_ι eta (n + 1) r.succ).symm
          let new : CommSq (outerLatchingStage X n r).ι (outerLatchingStageMap eta n r)
              (eta.app (op ⦋n + 1⦌)) (outerLatchingStage Y n r).ι :=
            CommSq.mk (outerLatchingStageMap_ι eta n r).symm
          have actual :=
              (RezkFiniteFromAllOperators.all_finite_from_original_operators eta hrows
                hoperators n r).2
          exact (hc_weakSquare_iff old new eX.hom (𝟙 _) eY.hom (𝟙 _)
            (by simpa using ex.symm) over (by simp) (by simpa using ey.symm)
            (by infer_instance) (by infer_instance) (by infer_instance)
                (by infer_instance)).mpr actual

end SSet.RezkSourceOverlapIncoming
