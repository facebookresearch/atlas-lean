/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerGeneral

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerGeneral`

Applies Euler's formula `euler_general` (`|V| - |E| + F = 1 + c`, with `F = faceCount G`) to
four concrete graphs and solves it for the face count: the single edge on `Fin 2` and the path
`0 - 1 - 2` (trees, `F = 1`), the 4-cycle `0 - 1 - 2 - 3 - 0` (the unit square, `F = 2`), and the
empty graph on `Fin 3` (three components, `F = 1`). Also applies
`euler_general_disconnected_components`, and the two edge-deletion lemmas: deleting the edge of
`Fin 2` (a bridge) adds a component and keeps `F`, and deleting the edge `{0, 1}` of the 4-cycle
(not a bridge) lowers `F` by one.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.EulerGeneral

open _root_.StatMech _root_.StatMech.Lattice _root_.SimpleGraph

/-- A connected graph has exactly one component. -/
theorem card_components_of_connected {V : Type*} {G : SimpleGraph V} (h : G.Connected) :
    Nat.card G.ConnectedComponent = 1 := by
  have := h.preconnected.subsingleton_connectedComponent
  exact Nat.card_of_subsingleton (G.connectedComponentMk h.nonempty.some)

/-- The adjacency relation of the 4-cycle `0 - 1 - 2 - 3 - 0`. -/
def cyc4Rel (i j : Fin 4) : Bool := (j = i + 1) || (i = j + 1)

/-- The 4-cycle, i.e. the unit square of `ℤ²` as an abstract graph. -/
def cyc4 : SimpleGraph (Fin 4) where
  Adj i j := cyc4Rel i j
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel cyc4.Adj := fun i j => inferInstanceAs (Decidable (cyc4Rel i j = true))

/-- The adjacency relation of the path `0 - 1 - 2`. -/
def path3Rel (i j : Fin 3) : Bool := (i.val + 1 = j.val) || (j.val + 1 = i.val)

/-- The path graph `0 - 1 - 2`. -/
def path3 : SimpleGraph (Fin 3) where
  Adj i j := path3Rel i j
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel path3.Adj := fun i j => inferInstanceAs (Decidable (path3Rel i j = true))

theorem cyc4_connected : cyc4.Connected := by
  have h : ∀ i : Fin 4, cyc4.Reachable 0 i := by
    have a : ∀ i : Fin 4, cyc4.Adj i (i + 1) := by decide
    intro i; fin_cases i
    · rfl
    · exact (a 0).reachable
    · exact (a 0).reachable.trans (a 1).reachable
    · exact (a 3).symm.reachable
  exact (connected_iff_exists_forall_reachable _).mpr ⟨0, h⟩

theorem path3_connected : path3.Connected := by
  have a01 : path3.Adj 0 1 := by decide
  have a12 : path3.Adj 1 2 := by decide
  refine (connected_iff_exists_forall_reachable _).mpr ⟨0, fun i => ?_⟩
  fin_cases i
  · rfl
  · exact a01.reachable
  · exact a01.reachable.trans a12.reachable

theorem cyc4_ncard : cyc4.edgeSet.ncard = 4 := by
  rw [Set.ncard_eq_toFinset_card']; decide

theorem path3_ncard : path3.edgeSet.ncard = 2 := by
  rw [Set.ncard_eq_toFinset_card']; decide

theorem top2_ncard : (⊤ : SimpleGraph (Fin 2)).edgeSet.ncard = 1 := by
  rw [Set.ncard_eq_toFinset_card']; decide

-- Euler's formula for the single edge: `2 - 1 + F = 1 + 1`, so `F = 1`.
example : faceCount (⊤ : SimpleGraph (Fin 2)) = 1 := by
  have h := euler_general (⊤ : SimpleGraph (Fin 2))
  rw [top2_ncard, card_components_of_connected connected_top, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h
  omega

-- Euler's formula for the path `0 - 1 - 2`: `3 - 2 + F = 1 + 1`, so `F = 1`.
example : faceCount path3 = 1 := by
  have h := euler_general path3
  rw [path3_ncard, card_components_of_connected path3_connected, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h
  omega

-- Euler's formula for the unit square: `4 - 4 + F = 1 + 1`, so `F = 2` (inside and outside).
theorem faceCount_cyc4 : faceCount cyc4 = 2 := by
  have h := euler_general cyc4
  rw [cyc4_ncard, card_components_of_connected cyc4_connected, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h
  omega

-- Euler's formula for the empty graph on `Fin 3`: `3 - 0 + F = 1 + 3`, so `F = 1`.
example : faceCount (⊥ : SimpleGraph (Fin 3)) = 1 := by
  have h := euler_general (⊥ : SimpleGraph (Fin 3))
  have hc : Nat.card (⊥ : SimpleGraph (Fin 3)).ConnectedComponent = 3 := by
    rw [← Nat.card_congr (Equiv.ofBijective (⊥ : SimpleGraph (Fin 3)).connectedComponentMk
      ⟨fun x y hxy => ?_, fun c => ?_⟩)]
    · simp
    · exact reachable_bot.mp (ConnectedComponent.eq.mp hxy)
    · induction c using ConnectedComponent.ind with | h v => exact ⟨v, rfl⟩
  rw [edgeSet_bot, Set.ncard_empty, hc, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

-- `euler_general_disconnected_components` recovers one component for the unit square.
example : (Nat.card cyc4.ConnectedComponent : ℤ) = 1 := by
  rw [euler_general_disconnected_components, cyc4_ncard, faceCount_cyc4, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

-- Deleting the edge `{0, 1}` of the unit square (not a bridge: `0 - 3 - 2 - 1` remains) lowers
-- the face count from `2` to `1` and keeps one component.
example : faceCount (cyc4.deleteEdges {s(0, 1)}) = 1 := by
  have he : s(0, 1) ∈ cyc4.edgeSet := by rw [mem_edgeSet]; decide
  have hr : (cyc4.deleteEdges {s(0, 1)}).Reachable 0 1 := by
    have h03 : (cyc4.deleteEdges {s(0, 1)}).Adj 0 3 := by
      rw [deleteEdges_adj, Set.mem_singleton_iff]; decide
    have h32 : (cyc4.deleteEdges {s(0, 1)}).Adj 3 2 := by
      rw [deleteEdges_adj, Set.mem_singleton_iff]; decide
    have h21 : (cyc4.deleteEdges {s(0, 1)}).Adj 2 1 := by
      rw [deleteEdges_adj, Set.mem_singleton_iff]; decide
    exact h03.reachable.trans (h32.reachable.trans h21.reachable)
  have h := (faceCount_deleteEdges_of_not_isBridge cyc4 he hr).1
  rw [faceCount_cyc4] at h
  omega

-- Deleting the only edge of `Fin 2` (a bridge) keeps the face count and adds a component.
example : Nat.card ((⊤ : SimpleGraph (Fin 2)).deleteEdges {s(0, 1)}).ConnectedComponent = 2 := by
  have he : s(0, 1) ∈ (⊤ : SimpleGraph (Fin 2)).edgeSet := by rw [mem_edgeSet]; decide
  have hbot : (⊤ : SimpleGraph (Fin 2)).deleteEdges {s(0, 1)} = ⊥ := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [Sym2.eq_swap]
  have hr : ¬ ((⊤ : SimpleGraph (Fin 2)).deleteEdges {s(0, 1)}).Reachable 0 1 := by
    rw [hbot, reachable_bot]; decide
  have h := (faceCount_deleteEdges_of_isBridge _ he hr).2
  rw [h, card_components_of_connected connected_top]

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.EulerGeneral
