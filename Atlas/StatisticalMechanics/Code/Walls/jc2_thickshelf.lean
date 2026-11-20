/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Walls.jc_runnoup
import Code.Lattice.EarExistence
import Code.Lattice.EarRemoval

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice








def jc2_downCell (v : Site 2) : Site 2 := v + ![0, -1]

@[simp] theorem jc2_downCell_eq (v : Site 2) : jc2_downCell v = v + ![0, -1] := rfl




theorem jc2_downCell_run (c : Site 2) (j : ℤ) :
    jc2_downCell (c + ![j, 0]) = c + ![j, -1] := by
  funext k; fin_cases k <;> · simp only [jc2_downCell, Pi.add_apply]; simp



theorem jc2_shelfCell_coord1 (c : Site 2) (j : ℤ) :
    (c + ![j, -1] : Site 2) 1 = c 1 - 1 := by
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; ring



theorem jc2_shelfCell_coord0 (c : Site 2) (j : ℤ) :
    (c + ![j, -1] : Site 2) 0 = c 0 + j := by
  simp only [Pi.add_apply, Matrix.cons_val_zero]










def jc2_FullyThick (K : Set (Site 2)) (c : Site 2) (len : ℤ) : Prop :=
  ∀ j : ℤ, 0 ≤ j → j ≤ len → jc2_downCell (c + ![j, 0]) ∈ K















theorem jc2_shelf_mem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hthick : jc2_FullyThick K c len) :
    ∀ j : ℤ, 0 ≤ j → j ≤ len → (c + ![j, -1] : Site 2) ∈ K := by
  intro j hj0 hj1
  have h := hthick j hj0 hj1
  rwa [jc2_downCell_run c j] at h





theorem jc2_shelf_adj_run (c : Site 2) (j : ℤ) :
    (hypercubicLattice 2).Adj (c + ![j, 0]) (c + ![j, -1]) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  have e0 : ((c + ![j, 0] : Site 2) 0 - (c + ![j, -1] : Site 2) 0) = 0 := by
    simp only [Pi.add_apply, Matrix.cons_val_zero]; ring
  have e1 : ((c + ![j, 0] : Site 2) 1 - (c + ![j, -1] : Site 2) 1) = 1 := by
    simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; ring
  rw [e0, e1]; decide





theorem jc2_shelf_below_topRow (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (_hrun : jc_IsTopRowRun K c len) (j : ℤ) :
    (c + ![j, -1] : Site 2) 1 < c 1 := by
  rw [jc2_shelfCell_coord1]; omega



theorem jc2_shelf_left_end (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hthick : jc2_FullyThick K c len) (hlen : 0 ≤ len) :
    (c + ![0, -1] : Site 2) ∈ K :=
  jc2_shelf_mem K c len hthick 0 (le_refl 0) hlen



theorem jc2_shelf_right_end (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hthick : jc2_FullyThick K c len) (hlen : 0 ≤ len) :
    (c + ![len, -1] : Site 2) ∈ K :=
  jc2_shelf_mem K c len hthick len hlen (le_refl len)
















theorem jc2_thickShelf (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) (hthick : jc2_FullyThick K c len) :
    (∀ j : ℤ, 0 ≤ j → j ≤ len → (c + ![j, -1] : Site 2) ∈ K) ∧
      (∀ j : ℤ, (hypercubicLattice 2).Adj (c + ![j, 0]) (c + ![j, -1])) ∧
      (∀ j : ℤ, (c + ![j, -1] : Site 2) 1 < c 1) :=
  ⟨jc2_shelf_mem K c len hthick,
   fun j => jc2_shelf_adj_run c j,
   fun j => jc2_shelf_below_topRow K c len hrun j⟩





theorem jc2_thickShelf_explicit (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) (hthick : jc2_FullyThick K c len) (hlen : 0 ≤ len) :
    (∀ j : ℤ, 0 ≤ j → j ≤ len → (c + ![j, -1] : Site 2) ∈ K) ∧
      (∀ j : ℤ, (hypercubicLattice 2).Adj (c + ![j, 0]) (c + ![j, -1])) ∧
      (∀ j : ℤ, (c + ![j, -1] : Site 2) 1 < c 1) ∧
      (c + ![0, -1] : Site 2) ∈ K ∧ (c + ![len, -1] : Site 2) ∈ K :=
  ⟨jc2_shelf_mem K c len hthick,
   fun j => jc2_shelf_adj_run c j,
   fun j => jc2_shelf_below_topRow K c len hrun j,
   jc2_shelf_left_end K c len hthick hlen,
   jc2_shelf_right_end K c len hthick hlen⟩














theorem jc2_domino_not_fullyThick : ¬ jc2_FullyThick domino (![0, 0] : Site 2) 1 := by
  intro h
  have hmem : jc2_downCell ((![0, 0] : Site 2) + ![0, 0]) ∈ domino := h 0 (le_refl 0) (by norm_num)
  rw [jc2_downCell_run] at hmem
  
  revert hmem
  apply not_mem_domino
  intro hd
  rcases hd with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
    · revert h1
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega



def jc2_block2 : Set (Site 2) :=
  {v | (v 0 = 0 ∨ v 0 = 1) ∧ (v 1 = 0 ∨ v 1 = 1)}





theorem jc2_block2_fullyThick : jc2_FullyThick jc2_block2 (![0, 1] : Site 2) 1 := by
  intro j hj0 hj1
  rw [jc2_downCell_run]
  
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
    · refine ⟨?_, ?_⟩
      · simp only [Pi.add_apply, Matrix.cons_val_zero]; omega
      · left; simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; ring




theorem jc2_block2_shelf_mem :
    ∀ j : ℤ, 0 ≤ j → j ≤ 1 → ((![0, 1] : Site 2) + ![j, -1]) ∈ jc2_block2 :=
  jc2_shelf_mem jc2_block2 (![0, 1] : Site 2) 1 jc2_block2_fullyThick

end Walls

end StatMech
