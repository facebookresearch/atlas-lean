/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalSuccessorSharpAndIncoming
import Lean.Elab.Tactic.Omega

/-!
# Sharpness and cell invariants of all finite skeleta

A bisimplicial map with sharp rows and weak operator-relative comparisons has a sharp map on every finite diagonal skeleton, with homotopy cartesian incoming squares for every cell in that stage. The inductive proof identifies old and newly attached cell maps and transports their incoming squares through the successor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkAllSkeletalInvariants
open SharpComparisonDraft RezkSkeletalCell RezkSkeletalSuccessor

private theorem hc_transport_eq {A X B Y : SSet.{u}}
    {f f' : A ⟶ X} {s : A ⟶ B} {p : X ⟶ Y} {g g' : B ⟶ Y}
    (sq : CommSq f s p g) (sq' : CommSq f' s p g') (hf : f = f') (hg : g = g')
    (hc : WeakEquivalence (pullback.lift f' s sq'.w ≫ comparison p g')) :
    WeakEquivalence (pullback.lift f s sq.w ≫ comparison p g) := by
  exact (RezkCompatiblePushout.hc_weakSquare_iff sq sq' (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id, Category.id_comp] using hf)
    (by simp) (by simp)
    (by simpa only [Category.comp_id, Category.id_comp] using hg)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr hc

/-- The old cell's composite is the SAME original cell in the later stage. -/
@[reassoc]
theorem cellToStage_comp (X : SimplicialObject SSet.{u}) {k n m : ℕ}
    (hkn : k ≤ n) (hnm : n ≤ m) :
    cellToStage X k n hkn ≫ diagonalFiltrationMap X hnm =
      cellToStage X k m (hkn.trans hnm) := by
  apply (cancel_mono (diagonalFiltration X m).ι).mp
  simp [Category.assoc, diagonalFiltrationMap, cellToStage_ι]

/-- The actual new native cell is the same finite-stage cell lift. -/
theorem newCell_eq (X : SimplicialObject SSet.{u}) (n : ℕ) :
    diagonalCellToFiltrationSucc X n = cellToStage X (n + 1) (n + 1) le_rfl := by
  apply (cancel_mono (diagonalFiltration X (n + 1)).ι).mp
  rw [diagonalCellToFiltrationSucc_ι, cellToStage_ι]

/-- The successor invariant derives ALL old-cell incoming assertions,
including the newly attached cell, from the actual preceding invariant. -/
theorem successor_invariant {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    (n : ℕ) (previous : stageCellInvariant eta n) : stageCellInvariant eta (n + 1) := by
  have result := successor_sharp_and_both_incoming eta hrows hoperators n previous
  refine ⟨result.1, ?_⟩
  intro k hk
  by_cases old : k ≤ n
  · have rectangle := (RezkIncomingHC.first_hc_iff_rectangle
      (cellToStage X k n old) (diagonalFiltrationMap X (Nat.le_succ n))
      (eta.app (op ⦋k⦌) ▷ Δ[k]) (diagonalFiltrationNatMap eta n)
      (diagonalFiltrationNatMap eta (n + 1))
      (cellToStage Y k n old) (diagonalFiltrationMap Y (Nat.le_succ n))
      (cellToStage_naturality eta k n old)
          (diagonalFiltrationMap_naturality eta (Nat.le_succ n)).symm
      previous.1 result.1 result.2.1).mp (previous.2 k old)
    let actual : CommSq (cellToStage X k (n + 1) hk) (eta.app (op ⦋k⦌) ▷ Δ[k])
        (diagonalFiltrationNatMap eta (n + 1)) (cellToStage Y k (n + 1) hk) :=
      CommSq.mk (cellToStage_naturality eta k (n + 1) hk)
    let pasted := (CommSq.mk (cellToStage_naturality eta k n old)).horiz_comp
      (CommSq.mk (diagonalFiltrationMap_naturality eta (Nat.le_succ n)).symm)
    exact hc_transport_eq actual pasted
      (cellToStage_comp X old (Nat.le_succ n)).symm
      (cellToStage_comp Y old (Nat.le_succ n)).symm rectangle
  · have eq : k = n + 1 := by omega
    subst k
    let actual : CommSq (cellToStage X (n + 1) (n + 1) hk)
        (eta.app (op ⦋n + 1⦌) ▷ Δ[n + 1]) (diagonalFiltrationNatMap eta (n + 1))
        (cellToStage Y (n + 1) (n + 1) hk) :=
      CommSq.mk (cellToStage_naturality eta (n + 1) (n + 1) hk)
    exact hc_transport_eq actual
      (CommSq.mk (diagonalCellToFiltrationSucc_naturality eta n).symm)
      (newCell_eq X n).symm (newCell_eq Y n).symm result.2.2

/-- The full finite skeletal invariant follows from the ORIGINAL inputs.
No stage Sharp, incoming family, total Sharp or diagonal-HF outcome is
supplied. Finite face/latching HC and the successor are proved internally. -/
theorem all_skeletal_sharp_and_cell_incoming
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f)) :
    ∀ n : ℕ, stageCellInvariant eta n := by
  intro n
  induction n with
  | zero => exact zero_stage_invariant eta hrows
  | succ n previous => exact successor_invariant eta hrows hoperators n previous

end SSet.RezkAllSkeletalInvariants
