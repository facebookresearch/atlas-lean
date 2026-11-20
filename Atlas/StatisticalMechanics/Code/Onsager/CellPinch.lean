/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.CellEuler











namespace StatMech.Onsager.CellPinch

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler




def pinchAt (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : Prop :=
  (v ∈ S ∧ (v.1 - 1, v.2 - 1) ∈ S ∧ (v.1 - 1, v.2) ∉ S ∧ (v.1, v.2 - 1) ∉ S) ∨
    ((v.1 - 1, v.2) ∈ S ∧ (v.1, v.2 - 1) ∈ S ∧ v ∉ S ∧ (v.1 - 1, v.2 - 1) ∉ S)

instance (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : Decidable (pinchAt S v) := by
  unfold pinchAt; infer_instance


def pinchW (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : ℤ := if pinchAt S v then 1 else 0


def pinchCount (S : Finset (ℤ × ℤ)) : ℤ := ∑ v ∈ cellVerts S, pinchW S v


theorem pinchAt_mem_cellVerts (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) (h : pinchAt S v) :
    v ∈ cellVerts S := by
  have hpos : 0 < cornerCount S v := by
    rw [cornerCount_eq_inter]
    apply Finset.card_pos.mpr
    rcases h with ⟨ha, _, _, _⟩ | ⟨hb, _, _, _⟩
    · exact ⟨v, by simp only [Finset.mem_inter, mem_insert, mem_singleton]; exact ⟨ha, by tauto⟩⟩
    · exact ⟨(v.1 - 1, v.2), by
        simp only [Finset.mem_inter, mem_insert, mem_singleton]; exact ⟨hb, by tauto⟩⟩
  exact (cornerCount_pos_iff_mem S v).mp hpos


theorem pinchAt_insert_of_notMem (S : Finset (ℤ × ℤ)) (c v : ℤ × ℤ) (hv : v ∉ cornersOf c) :
    pinchAt (insert c S) v = pinchAt S v := by
  have hne : ∀ w : ℤ × ℤ, w ∈ ({v, (v.1 - 1, v.2), (v.1, v.2 - 1), (v.1 - 1, v.2 - 1)}
      : Finset (ℤ × ℤ)) → c ≠ w := by
    intro w hw hcw
    apply hv
    rw [mem_cornersOf_iff]
    subst hcw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with h | h | h | h <;> rw [h] <;> tauto
  have hmem : ∀ w : ℤ × ℤ, w ∈ ({v, (v.1 - 1, v.2), (v.1, v.2 - 1), (v.1 - 1, v.2 - 1)}
      : Finset (ℤ × ℤ)) → (w ∈ insert c S ↔ w ∈ S) := by
    intro w hw
    rw [Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact absurd h.symm (hne w hw)
      · exact h
    · exact fun h => Or.inr h
  unfold pinchAt
  have e1 := hmem v (by simp)
  have e2 := hmem (v.1 - 1, v.2) (by simp)
  have e3 := hmem (v.1, v.2 - 1) (by simp)
  have e4 := hmem (v.1 - 1, v.2 - 1) (by simp)
  simp only [e1, e2, e3, e4]


theorem pinchW_zero_of_notMem (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) (hv : v ∉ cellVerts S) :
    pinchW S v = 0 := by
  unfold pinchW
  rw [if_neg (fun h => hv (pinchAt_mem_cellVerts S v h))]



theorem pinchCount_insert (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∉ S) :
    pinchCount (insert c S)
      = pinchCount S + ∑ v ∈ cornersOf c, (pinchW (insert c S) v - pinchW S v) := by
  have hsub : pinchCount S = ∑ v ∈ cornersOf c ∪ cellVerts S, pinchW S v := by
    unfold pinchCount
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hvnot
    exact pinchW_zero_of_notMem S v hvnot
  have hexpand :
      ∑ v ∈ cornersOf c ∪ cellVerts S,
          (if v ∈ cornersOf c then pinchW (insert c S) v - pinchW S v else 0)
        = ∑ v ∈ cornersOf c, (pinchW (insert c S) v - pinchW S v) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_left]
  rw [hsub]
  show ∑ v ∈ cellVerts (insert c S), pinchW (insert c S) v = _
  rw [cellVerts_insert, ← hexpand, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : v ∈ cornersOf c
  · simp only [if_pos h]; ring
  · simp only [if_neg h, add_zero, pinchW, pinchAt_insert_of_notMem S c v h]

end StatMech.Onsager.CellPinch
