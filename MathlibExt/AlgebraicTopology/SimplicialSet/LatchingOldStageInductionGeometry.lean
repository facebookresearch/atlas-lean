/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.LatchingOldStageMaps
import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteStageInductionGeometry
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Initial and successor comparisons for preceding latching pieces

The piece before the first degeneracy attachment is empty, so the preceding diagonal stage invariant gives its weak incoming comparison. At a successor attachment, the before-piece comparison is transported from the corresponding prior finite-stage comparison through the explicit equality of their subcomplexes and maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkLatchingOldStage
open SharpComparisonDraft RezkSkeletalCell RezkCompatiblePushout

theorem before_zero (X : SimplicialObject SSet.{u}) (n : ℕ) :
    outerLatchingStageBefore X n 0 = ⊥ := by
  apply bot_unique
  intro a x hx
  simp only [outerLatchingStageBefore, Subfunctor.iSup_obj, Set.mem_iUnion] at hx
  obtain ⟨j, hj, hx⟩ := hx
  simp only [Fin.lt_def, Fin.val_zero] at hj
  exact (Nat.not_lt_zero _) hj

/-- The actual empty before-stage is HC; no before-stage output is supplied. -/
theorem before_zero_hc {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (previous : stageCellInvariant eta n) :
    WeakEquivalence
      (pullback.lift (beforeToOld X n 0) (outerLatchingStageBeforeMap eta n 0 ▷ Δ[n + 1])
        (beforeToOld_naturality eta n 0) ≫
        comparison (diagonalFiltrationNatMap eta n) (beforeToOld Y n 0)) := by
  have initX : IsInitial ((outerLatchingStageBefore X n 0 : SSet.{u}) ⊗ Δ[n + 1]) := by
    rw [before_zero]
    exact (Subcomplex.isInitialBot (X := X.obj (op ⦋n + 1⦌))).isInitialObj
      (tensorRight (Δ[n + 1] : SSet.{u})) _
  have initY : IsInitial ((outerLatchingStageBefore Y n 0 : SSet.{u}) ⊗ Δ[n + 1]) := by
    rw [before_zero]
    exact (Subcomplex.isInitialBot (X := Y.obj (op ⦋n + 1⦌))).isInitialObj
      (tensorRight (Δ[n + 1] : SSet.{u})) _
  exact RezkEmptyFace.initialSquare_hc initX initY (beforeToOld X n 0)
    (outerLatchingStageBeforeMap eta n 0 ▷ Δ[n + 1]) (diagonalFiltrationNatMap eta n)
    (beforeToOld Y n 0) previous.1

/-- The actual prior finite stage is the source of the next before-stage.
Only the previously derived finite HC is carried through its equality Isos. -/
theorem before_succ_hc_of_previous {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1))
    (prior : WeakEquivalence
      (pullback.lift (stageToOld X (n + 1) r.castSucc)
        (outerLatchingStageMap eta (n + 1) r.castSucc ▷ Δ[n + 2])
        (stageToOld_naturality eta (n + 1) r.castSucc) ≫
        comparison (diagonalFiltrationNatMap eta (n + 1)) (stageToOld Y (n + 1) r.castSucc))) :
    WeakEquivalence
      (pullback.lift (beforeToOld X (n + 1) r.succ)
        (outerLatchingStageBeforeMap eta (n + 1) r.succ ▷ Δ[n + 2])
        (beforeToOld_naturality eta (n + 1) r.succ) ≫
        comparison (diagonalFiltrationNatMap eta (n + 1)) (beforeToOld Y (n + 1) r.succ)) := by
  let eX := Subcomplex.eqToIso (RezkFiniteStageGeometry.before_succ_eq X n r)
  let eY := Subcomplex.eqToIso (RezkFiniteStageGeometry.before_succ_eq Y n r)
  have xfactor : (eX.hom ▷ Δ[n + 2]) ≫ stageToOld X (n + 1) r.castSucc =
      beforeToOld X (n + 1) r.succ := by
    apply (cancel_mono (diagonalFiltration X (n + 1)).ι).mp
    rw [Category.assoc, stageToOld_ι, beforeToOld_ι, ← Category.assoc, ← comp_whiskerRight]
    simp [eX, Subcomplex.eqToIso]
  have yfactor : (eY.hom ▷ Δ[n + 2]) ≫ stageToOld Y (n + 1) r.castSucc =
      beforeToOld Y (n + 1) r.succ := by
    apply (cancel_mono (diagonalFiltration Y (n + 1)).ι).mp
    rw [Category.assoc, stageToOld_ι, beforeToOld_ι, ← Category.assoc, ← comp_whiskerRight]
    simp [eY, Subcomplex.eqToIso]
  have maps : (eX.hom ▷ Δ[n + 2]) ≫ (outerLatchingStageMap eta (n + 1) r.castSucc ▷ Δ[n + 2]) =
      (outerLatchingStageBeforeMap eta (n + 1) r.succ ▷ Δ[n + 2]) ≫ (eY.hom ▷ Δ[n + 2]) := by
    simp only [← comp_whiskerRight]
    exact congrArg (fun f => f ▷ (Δ[n + 2] : SSet.{u}))
      (RezkFiniteStageGeometry.beforeArrowIso eta n r).hom.w
  let old : CommSq (beforeToOld X (n + 1) r.succ)
      (outerLatchingStageBeforeMap eta (n + 1) r.succ ▷ Δ[n + 2])
      (diagonalFiltrationNatMap eta (n + 1)) (beforeToOld Y (n + 1) r.succ) :=
    CommSq.mk (beforeToOld_naturality eta (n + 1) r.succ)
  let new : CommSq (stageToOld X (n + 1) r.castSucc)
      (outerLatchingStageMap eta (n + 1) r.castSucc ▷ Δ[n + 2])
      (diagonalFiltrationNatMap eta (n + 1)) (stageToOld Y (n + 1) r.castSucc) :=
    CommSq.mk (stageToOld_naturality eta (n + 1) r.castSucc)
  exact (hc_weakSquare_iff old new (eX.hom ▷ Δ[n + 2]) (𝟙 _)
    (eY.hom ▷ Δ[n + 2]) (𝟙 _)
    (by simpa using xfactor.symm) maps (by simp) (by simpa using yfactor.symm)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr prior

end SSet.RezkLatchingOldStage
