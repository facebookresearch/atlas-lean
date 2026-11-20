/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.LeftCornerN
import Code.Onsager.LeftCornerE
import Code.Onsager.LeftCornerW
import Code.Onsager.LeftCornerS
import Code.Onsager.StraightCorner
import Code.Onsager.WalkCornerSum
import Code.Onsager.CellGaussBonnetGlobal










namespace StatMech.Onsager.MasterCorner

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.InteriorCells StatMech.Onsager.Orientation StatMech.Onsager.LeftCornerN
  StatMech.Onsager.LeftCornerE StatMech.Onsager.LeftCornerW StatMech.Onsager.LeftCornerS
  StatMech.Onsager.StraightCorner StatMech.Onsager.WalkCornerSum StatMech.Onsager.CellPinch
  StatMech.Onsager.CellGaussBonnetGlobal

variable {n : ℕ} [NeZero n]



theorem cornerWeight_master (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) (i : Fin n) :
    cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1)))
      = (if leftParity d 0 = 1 then (1 : ℤ) else -1) * (if d (i + 1) - d i = 1 then 1 else 0) := by
  rcases hreflexfree i with h0 | h1
  · 
    have hst : d (i + 1) = d i := by rw [sub_eq_zero] at h0; exact h0
    rw [cornerWeight_straight d hclosed hsimple i hst,
      if_neg (show ¬ (d (i + 1) - d i = 1) from by rw [h0]; decide), mul_zero]
  · 
    rw [if_pos h1, mul_one]
    have hlp : rayParity d (leftCell (d (i + 1)) (pos d (i + 1))).1
          (leftCell (d (i + 1)) (pos d (i + 1))).2 = leftParity d 0 :=
      leftParity_const d hclosed hsimple hreflexfree (i + 1)
    have hei : d i = d (i + 1) - 1 := by
      rw [eq_sub_iff_add_eq, sub_eq_iff_eq_add.mp h1]; abel
    rcases (by decide : ∀ w : Fin 4, w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) (d (i + 1)) with
      hd | hd | hd | hd
    · rw [cornerWeight_leftTurn_E d hclosed hsimple hn i (by rw [hei, hd]; decide) hd, hlp]
    · rw [cornerWeight_leftTurn_N d hclosed hsimple hn i (by rw [hei, hd]; decide) hd, hlp]
    · rw [cornerWeight_leftTurn_W d hclosed hsimple hn i (by rw [hei, hd]; decide) hd, hlp]
    · rw [cornerWeight_leftTurn_S d hclosed hsimple hn i (by rw [hei, hd]; decide) hd, hlp]



theorem cornerDiff_eq_weight_mul_cc (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cornerDiff (interiorCells d hclosed)
      = (if leftParity d 0 = 1 then (1 : ℤ) else -1) * (cc d : ℤ) := by
  rw [cornerDiff_interior_eq_walk_sum d hclosed hsimple,
    ← Equiv.sum_comp (Equiv.addRight (1 : Fin n))
      (fun k => cornerWeight (cornerCount (interiorCells d hclosed) (pos d k)))]
  simp only [Equiv.coe_addRight]
  rw [Finset.sum_congr rfl (fun i _ => cornerWeight_master d hclosed hsimple hn hreflexfree i),
    ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_boole]
  rfl





theorem cc_eq_four (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (hpinch : pinchCount (interiorCells d hclosed) = 0)
    (hchi : eulerChar (interiorCells d hclosed) = 1) :
    cc d = 4 := by
  have h1 := cornerDiff_eq_weight_mul_cc d hclosed hsimple hn hreflexfree
  have h2 := cornerDiff_eq (interiorCells d hclosed)
  rw [hchi, hpinch] at h2
  norm_num at h2
  have h3 : (if leftParity d 0 = 1 then (1 : ℤ) else -1) * (cc d : ℤ) = 4 := h1.symm.trans h2
  have hcc4 : 4 ≤ cc d := four_le_cc d hclosed hreflexfree
  by_cases hW : leftParity d 0 = 1
  · rw [if_pos hW, one_mul] at h3; omega
  · rw [if_neg hW] at h3; omega

end StatMech.Onsager.MasterCorner
