/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.MasterCorner
import Code.Onsager.PinchFree
import Code.Onsager.CellGaussBonnetGlobal
import Code.Onsager.WalkCellBoundary
import Code.Onsager.WalkCellRegion
import Code.Onsager.CellEulerFaithful

















namespace StatMech.Onsager.UmlaufsatzFinal

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellPinch StatMech.Onsager.InteriorCells StatMech.Onsager.Orientation
  StatMech.Onsager.MasterCorner StatMech.Onsager.PinchFree
  StatMech.Onsager.CellGaussBonnetGlobal

variable {m : ℕ}


theorem leftCell_bridge (d : Fin (m + 3) → Fin 4) (k : Fin (m + 3)) :
    Orientation.leftCell (d k) (pos d k) = WalkCellBoundary.leftCell d k := by
  rw [WalkCellBoundary.leftCell]
  match hd : d k with
  | 0 => simp [Orientation.leftCell, hd]
  | 1 => simp [Orientation.leftCell, hd]
  | 2 => simp [Orientation.leftCell, hd]
  | 3 => simp [Orientation.leftCell, hd]


theorem leftParity_zero (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    leftParity d 0 = 1 := by
  unfold Orientation.leftParity
  rw [leftCell_bridge d 0]
  exact WalkCellBoundary.leftCell_parity_one d hclosed hsimple hreflexfree 0


theorem interiorCells_bridge (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    InteriorCells.interiorCells d hclosed
      = WalkCellRegion.interiorCells d hclosed hsimple hreflexfree := by
  ext p
  rw [InteriorCells.mem_interiorCells, WalkCellRegion.mem_interiorCells_iff_rayParity]


theorem cc_eq_four' (d : Fin (m + 3) → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cc d = 4 := by
  have hn : 3 ≤ m + 3 := by omega
  have hW : leftParity d 0 = 1 := leftParity_zero d hclosed hsimple hreflexfree
  have hle : eulerChar (InteriorCells.interiorCells d hclosed) ≤ 1 := by
    rw [interiorCells_bridge d hclosed hsimple hreflexfree]
    exact CellEulerFaithful.eulerChar_interiorCells_le_one d hclosed hsimple hreflexfree
  have hpinch := PinchFree.pinchCount_eq_zero d hclosed hsimple hn
  have h1 := MasterCorner.cornerDiff_eq_weight_mul_cc d hclosed hsimple hn hreflexfree
  have h2 := cornerDiff_eq (InteriorCells.interiorCells d hclosed)
  rw [hpinch] at h2
  rw [if_pos hW, one_mul] at h1
  have hkey : (cc d : ℤ) = 4 * eulerChar (InteriorCells.interiorCells d hclosed) := by
    rw [← h1, h2]; ring
  have hcc4 : 4 ≤ cc d := four_le_cc d hclosed hreflexfree
  omega


theorem cc_eq_four {n : ℕ} [NeZero n] (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cc d = 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact cc_eq_four' d hclosed hsimple hreflexfree


theorem stepOf_ne_zero (w : Fin 4) : stepOf w ≠ 0 := by fin_cases w <;> decide



theorem three_le_n {n : ℕ} [NeZero n] (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) : 3 ≤ n := by
  have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  by_contra hlt
  push_neg at hlt
  interval_cases n
  · rw [Fin.sum_univ_one] at hclosed
    exact stepOf_ne_zero (d 0) hclosed
  · have ht0 := hreflexfree 0
    have ht1 := hreflexfree 1
    rw [Fin.sum_univ_two] at hclosed
    simp only [show ((0 : Fin 2) + 1 = 1) from by decide,
      show ((1 : Fin 2) + 1 = 0) from by decide] at ht0 ht1
    obtain ⟨a, ha⟩ : ∃ a, d 0 = a := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, d 1 = b := ⟨_, rfl⟩
    rw [ha, hb] at hclosed ht0 ht1
    fin_cases a <;> fin_cases b <;> revert hclosed ht0 ht1 <;> decide



theorem cc_eq_four_unconditional {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cc d = 4 :=
  cc_eq_four d hclosed hsimple (three_le_n d hclosed hreflexfree) hreflexfree



theorem hnodbl_discharged {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    Function.Injective (pos d) → cc d < 8 :=
  fun hsimple => by rw [cc_eq_four_unconditional d hclosed hsimple hreflexfree]; norm_num

end StatMech.Onsager.UmlaufsatzFinal
