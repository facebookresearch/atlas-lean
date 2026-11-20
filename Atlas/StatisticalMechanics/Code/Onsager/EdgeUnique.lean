/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.RayFlipV
import Code.Onsager.RayFlipH










namespace StatMech.Onsager.EdgeUnique

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity StatMech.Onsager.RayFlipV StatMech.Onsager.RayFlipH

variable {n : ℕ} [NeZero n]


theorem not_add_two_self (hn : 3 ≤ n) (k : Fin n) : k + 1 + 1 ≠ k := by
  intro h
  have hcancel : (1 + 1 : Fin n) = 0 := by
    have hz : k + (1 + 1 : Fin n) = k + 0 := by rw [add_zero, ← add_assoc]; exact h
    exact add_left_cancel hz
  have hv := congrArg Fin.val hcancel
  rw [Fin.val_add, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < n),
    Nat.mod_eq_of_lt (by omega : 1 + 1 < n)] at hv
  omega


theorem midSet_endpoints (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (a b : ℤ)
    (k : Fin n) (hk : k ∈ midSet d a b) :
    (pos d k = (a, b) ∧ pos d (k + 1) = (a + 1, b))
      ∨ (pos d k = (a + 1, b) ∧ pos d (k + 1) = (a, b)) := by
  simp only [midSet, mem_filter, mem_univ, true_and] at hk
  obtain ⟨hH, hm, hy⟩ := hk
  have hyc := horiz_y_const d hclosed k hH
  rcases horiz_x_step d hclosed k hH with hx | hx
  · left; exact ⟨Prod.ext (by omega) hy, Prod.ext (by omega) (by rw [hyc, hy])⟩
  · right; exact ⟨Prod.ext (by omega) hy, Prod.ext (by omega) (by rw [hyc, hy])⟩


theorem straddleSet_endpoints (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (a b : ℤ)
    (k : Fin n) (hk : k ∈ straddleSet d a b) :
    (pos d k = (a + 1, b) ∧ pos d (k + 1) = (a + 1, b + 1))
      ∨ (pos d k = (a + 1, b + 1) ∧ pos d (k + 1) = (a + 1, b)) := by
  simp only [straddleSet, mem_filter, mem_univ, true_and] at hk
  obtain ⟨hV, hx, hmn, hmx⟩ := hk
  have hxc := vert_x_const d hclosed k hV
  rcases vert_y_step d hclosed k hV with hy | hy
  · left; exact ⟨Prod.ext hx (by omega), Prod.ext (by rw [hxc, hx]) (by omega)⟩
  · right; exact ⟨Prod.ext hx (by omega), Prod.ext (by rw [hxc, hx]) (by omega)⟩


theorem midSet_card_le_one (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) (a b : ℤ) :
    (midSet d a b).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro k hk k' hk'
  rcases midSet_endpoints d hclosed a b k hk with ⟨hk1, hk2⟩ | ⟨hk1, hk2⟩ <;>
    rcases midSet_endpoints d hclosed a b k' hk' with ⟨hk1', hk2'⟩ | ⟨hk1', hk2'⟩
  · exact hsimple (hk1.trans hk1'.symm)
  · 
    have e1 : k = k' + 1 := hsimple (hk1.trans hk2'.symm)
    have e2 : k + 1 = k' := hsimple (hk2.trans hk1'.symm)
    exact absurd (by rw [e1] at e2; exact e2) (not_add_two_self hn k')
  · have e1 : k = k' + 1 := hsimple (hk1.trans hk2'.symm)
    have e2 : k + 1 = k' := hsimple (hk2.trans hk1'.symm)
    exact absurd (by rw [e1] at e2; exact e2) (not_add_two_self hn k')
  · exact hsimple (hk1.trans hk1'.symm)


theorem straddleSet_card_le_one (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) (a b : ℤ) :
    (straddleSet d a b).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro k hk k' hk'
  rcases straddleSet_endpoints d hclosed a b k hk with ⟨hk1, hk2⟩ | ⟨hk1, hk2⟩ <;>
    rcases straddleSet_endpoints d hclosed a b k' hk' with ⟨hk1', hk2'⟩ | ⟨hk1', hk2'⟩
  · exact hsimple (hk1.trans hk1'.symm)
  · have e1 : k = k' + 1 := hsimple (hk1.trans hk2'.symm)
    have e2 : k + 1 = k' := hsimple (hk2.trans hk1'.symm)
    exact absurd (by rw [e1] at e2; exact e2) (not_add_two_self hn k')
  · have e1 : k = k' + 1 := hsimple (hk1.trans hk2'.symm)
    have e2 : k + 1 = k' := hsimple (hk2.trans hk1'.symm)
    exact absurd (by rw [e1] at e2; exact e2) (not_add_two_self hn k')
  · exact hsimple (hk1.trans hk1'.symm)


theorem midSet_card_odd_of_mem (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) (a b : ℤ)
    (k : Fin n) (hk : k ∈ midSet d a b) :
    (midSet d a b).card % 2 = 1 := by
  have hle := midSet_card_le_one d hclosed hsimple hn a b
  have hpos : 1 ≤ (midSet d a b).card := Finset.card_pos.mpr ⟨k, hk⟩
  omega


theorem straddleSet_card_odd_of_mem (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) (a b : ℤ)
    (k : Fin n) (hk : k ∈ straddleSet d a b) :
    (straddleSet d a b).card % 2 = 1 := by
  have hle := straddleSet_card_le_one d hclosed hsimple hn a b
  have hpos : 1 ≤ (straddleSet d a b).card := Finset.card_pos.mpr ⟨k, hk⟩
  omega

end StatMech.Onsager.EdgeUnique
