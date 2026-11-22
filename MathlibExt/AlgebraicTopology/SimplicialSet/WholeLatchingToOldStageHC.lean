/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.LatchingOldStageUnionHC

/-!
# Full latching comparisons into the preceding diagonal skeleton

For sharp row maps with weak relative comparisons for every simplex operator, the preceding diagonal stage invariant yields weak comparisons for all finite latching-stage maps into that skeleton. The last-stage identification then gives the natural whole-latching map and its weak pullback-to-homotopy-pullback comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkLatchingOldStage
open SharpComparisonDraft RezkSkeletalCell RezkCompatiblePushout

/-- Every actual finite degeneracy union is incoming HC into the old stage.
This is the native Fin induction, with no supplied finite-stage HC family. -/
theorem every_finite_latching_to_old_hc {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    (n : ℕ) (previous : stageCellInvariant eta n) :
    ∀ r : Fin (n + 1), WeakEquivalence
      (pullback.lift (stageToOld X n r) (outerLatchingStageMap eta n r ▷ Δ[n + 1])
        (stageToOld_naturality eta n r) ≫
        comparison (diagonalFiltrationNatMap eta n) (stageToOld Y n r)) := by
  cases n with
  | zero =>
      intro r
      have hr : r = 0 := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ r.isLt)
      subst r
      exact stage_hc_from_actual_before eta hrows hoperators 0 0 previous
          (before_zero_hc eta 0 previous)
  | succ n =>
      apply Fin.induction
      · exact stage_hc_from_actual_before eta hrows hoperators (n + 1) 0 previous
          (before_zero_hc eta (n + 1) previous)
      · intro r prior
        exact stage_hc_from_actual_before eta hrows hoperators (n + 1) r.succ previous
          (before_succ_hc_of_previous eta n r prior)

@[reassoc]
theorem wholeToOld_naturality {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :
    wholeToOld X n ≫ diagonalFiltrationNatMap eta n =
      (outerLatchingMap eta (n + 1) ▷ Δ[n + 1]) ≫ wholeToOld Y n := by
  apply (cancel_mono (diagonalFiltration Y n).ι).mp
  simp only [Category.assoc, diagonalFiltrationNatMap_ι, wholeToOld_ι_assoc, wholeToOld_ι]
  rw [← diagonalCellMap_naturality]
  simp only [tensorHom_id, ← Category.assoc, ← comp_whiskerRight, outerLatchingMap_ι]

/-- The whole ORIGINAL latching coefficient cell is HC to the preceding
skeleton. It is the last derived finite stage, transported through both
actual equality Isos; no whole-latching HC outcome is a premise. -/
theorem whole_latching_to_old_hc {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    (n : ℕ) (previous : stageCellInvariant eta n) :
    WeakEquivalence
      (pullback.lift (wholeToOld X n) (outerLatchingMap eta (n + 1) ▷ Δ[n + 1])
        (wholeToOld_naturality eta n) ≫
        comparison (diagonalFiltrationNatMap eta n) (wholeToOld Y n)) := by
  let eX := RezkFullLatching.lastStageIso X n
  let eY := RezkFullLatching.lastStageIso Y n
  have hx : (eX.hom ▷ Δ[n + 1]) ≫ wholeToOld X n = stageToOld X n (Fin.last n) := by
    apply (cancel_mono (diagonalFiltration X n).ι).mp
    rw [Category.assoc, wholeToOld_ι, stageToOld_ι, ← Category.assoc, ← comp_whiskerRight]
    simp only [eX, RezkFullLatching.lastStageIso_hom_ι]
  have hy : (eY.hom ▷ Δ[n + 1]) ≫ wholeToOld Y n = stageToOld Y n (Fin.last n) := by
    apply (cancel_mono (diagonalFiltration Y n).ι).mp
    rw [Category.assoc, wholeToOld_ι, stageToOld_ι, ← Category.assoc, ← comp_whiskerRight]
    simp only [eY, RezkFullLatching.lastStageIso_hom_ι]
  have hm : (eX.hom ▷ Δ[n + 1]) ≫ (outerLatchingMap eta (n + 1) ▷ Δ[n + 1]) =
      (outerLatchingStageMap eta n (Fin.last n) ▷ Δ[n + 1]) ≫ (eY.hom ▷ Δ[n + 1]) := by
    simp only [← comp_whiskerRight]
    exact congrArg (fun f => f ▷ (Δ[n + 1] : SSet.{u}))
        (RezkFullLatching.lastStageIso_naturality eta n)
  let old : CommSq (stageToOld X n (Fin.last n))
      (outerLatchingStageMap eta n (Fin.last n) ▷ Δ[n + 1])
      (diagonalFiltrationNatMap eta n) (stageToOld Y n (Fin.last n)) :=
    CommSq.mk (stageToOld_naturality eta n (Fin.last n))
  let new : CommSq (wholeToOld X n) (outerLatchingMap eta (n + 1) ▷ Δ[n + 1])
      (diagonalFiltrationNatMap eta n) (wholeToOld Y n) := CommSq.mk (wholeToOld_naturality eta n)
  have actual := every_finite_latching_to_old_hc eta hrows hoperators n previous (Fin.last n)
  exact (hc_weakSquare_iff old new (eX.hom ▷ Δ[n + 1]) (𝟙 _)
    (eY.hom ▷ Δ[n + 1]) (𝟙 _)
    (by simpa using hx.symm) hm (by simp) (by simpa using hy.symm)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mp actual

end SSet.RezkLatchingOldStage
