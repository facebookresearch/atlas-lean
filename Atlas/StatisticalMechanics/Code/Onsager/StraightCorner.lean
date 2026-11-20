/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.EdgeUnique
import Code.Onsager.WalkCellBridge
import Code.Onsager.Orientation









namespace StatMech.Onsager.StraightCorner

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity StatMech.Onsager.RayFlipV StatMech.Onsager.RayFlipH
  StatMech.Onsager.EdgeUnique StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.InteriorCells StatMech.Onsager.WalkCellBridge StatMech.Onsager.Orientation

variable {n : ℕ} [NeZero n]

theorem not_isVert_of_isHoriz {w : Fin 4} (h : isHorizEdge w) : ¬ isVertEdge w := by
  rcases h with h | h <;> rw [h] <;> decide

theorem not_isHoriz_of_isVert {w : Fin 4} (h : isVertEdge w) : ¬ isHorizEdge w := by
  rcases h with h | h <;> rw [h] <;> decide


theorem cornerWeight_eq_zero_of_two_dvd
    (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (v : ℤ × ℤ)
    (hdvd : 2 ∣ cornerCount (interiorCells d hclosed) v) :
    cornerWeight (cornerCount (interiorCells d hclosed) v) = 0 := by
  have hne1 : cornerCount (interiorCells d hclosed) v ≠ 1 := by omega
  have hne3 : cornerCount (interiorCells d hclosed) v ≠ 3 := by omega
  unfold cornerWeight
  rw [if_neg hne1, if_neg hne3]; ring

theorem cornerWeight_straight_horiz (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (i : Fin n)
    (hstraight : d (i + 1) = d i) (hh : isHorizEdge (d i)) :
    cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = 0 := by
  set vx := (pos d (i + 1)).1 with hvx
  set vy := (pos d (i + 1)).2 with hvy
  have hpe : pos d (i + 1) = (vx, vy) := Prod.ext hvx.symm hvy.symm
  have hhi1 : isHorizEdge (d (i + 1)) := by rw [hstraight]; exact hh
  
  have hNW : rayParity d (vx - 1) vy = rayParity d vx vy := by
    have hstr : ∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = (vx - 1) + 1 →
        ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ vy ∧ vy < max ((pos d k).2) ((pos d (k + 1)).2)) := by
      intro k hvk hxk ⟨hmn, hmx⟩
      have hxc := vert_x_const d hclosed k hvk
      rcases vert_y_step d hclosed k hvk with hy | hy
      · have hk0 : pos d k = pos d (i + 1) := by rw [hpe, Prod.ext_iff]; exact ⟨by omega, by omega⟩
        rw [hsimple hk0] at hvk; exact not_isVert_of_isHoriz hhi1 hvk
      · have hk1 : pos d (k + 1) = pos d (i + 1) := by
          rw [hpe, Prod.ext_iff]; exact ⟨by rw [hxc]; omega, by omega⟩
        have hki : k = i := add_right_cancel (hsimple hk1)
        rw [hki] at hvk; exact not_isVert_of_isHoriz hh hvk
    have h := rayParity_hstep d hclosed (vx - 1) vy hstr
    rwa [show vx - 1 + 1 = vx from by ring] at h
  
  have hSW : rayParity d (vx - 1) (vy - 1) = rayParity d vx (vy - 1) := by
    have hstr : ∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = (vx - 1) + 1 →
        ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ vy - 1 ∧
           vy - 1 < max ((pos d k).2) ((pos d (k + 1)).2)) := by
      intro k hvk hxk ⟨hmn, hmx⟩
      have hxc := vert_x_const d hclosed k hvk
      rcases vert_y_step d hclosed k hvk with hy | hy
      · have hk1 : pos d (k + 1) = pos d (i + 1) := by
          rw [hpe, Prod.ext_iff]; exact ⟨by rw [hxc]; omega, by omega⟩
        have hki : k = i := add_right_cancel (hsimple hk1)
        rw [hki] at hvk; exact not_isVert_of_isHoriz hh hvk
      · have hk0 : pos d k = pos d (i + 1) := by rw [hpe, Prod.ext_iff]; exact ⟨by omega, by omega⟩
        rw [hsimple hk0] at hvk; exact not_isVert_of_isHoriz hhi1 hvk
    have h := rayParity_hstep d hclosed (vx - 1) (vy - 1) hstr
    rwa [show vx - 1 + 1 = vx from by ring] at h
  apply cornerWeight_eq_zero_of_two_dvd d hclosed (pos d (i + 1))
  have hz : (cornerCount (interiorCells d hclosed) (pos d (i + 1)) : ℤ)
      = 2 * ((if rayParity d vx vy = 1 then (1 : ℤ) else 0)
        + (if rayParity d vx (vy - 1) = 1 then 1 else 0)) := by
    rw [hpe, cornerCount_interior_eq d hclosed vx vy, hNW, hSW]; ring
  have : (2 : ℤ) ∣ (cornerCount (interiorCells d hclosed) (pos d (i + 1)) : ℤ) := ⟨_, hz⟩
  exact_mod_cast this

theorem cornerWeight_straight_vert (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (i : Fin n)
    (hstraight : d (i + 1) = d i) (hv : isVertEdge (d i)) :
    cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = 0 := by
  set vx := (pos d (i + 1)).1 with hvx
  set vy := (pos d (i + 1)).2 with hvy
  have hpe : pos d (i + 1) = (vx, vy) := Prod.ext hvx.symm hvy.symm
  have hvi1 : isVertEdge (d (i + 1)) := by rw [hstraight]; exact hv
  
  have hSE : rayParity d vx (vy - 1) = rayParity d vx vy := by
    have hstr : ∀ k : Fin n, isHorizEdge (d k) →
        min ((pos d k).1) ((pos d (k + 1)).1) = vx → (pos d k).2 ≠ (vy - 1) + 1 := by
      intro k hhk hmk hyk
      rw [show (vy - 1) + 1 = vy from by ring] at hyk
      have hyc := horiz_y_const d hclosed k hhk
      rcases horiz_x_step d hclosed k hhk with hx | hx
      · have hk0 : pos d k = pos d (i + 1) := by rw [hpe, Prod.ext_iff]; exact ⟨by omega, by omega⟩
        rw [hsimple hk0] at hhk; exact not_isHoriz_of_isVert hvi1 hhk
      · have hk1 : pos d (k + 1) = pos d (i + 1) := by
          rw [hpe, Prod.ext_iff]; exact ⟨by omega, by rw [hyc]; omega⟩
        have hki : k = i := add_right_cancel (hsimple hk1)
        rw [hki] at hhk; exact not_isHoriz_of_isVert hv hhk
    have h := rayParity_vstep d vx (vy - 1) hstr
    rwa [show vy - 1 + 1 = vy from by ring] at h
  
  have hSW : rayParity d (vx - 1) (vy - 1) = rayParity d (vx - 1) vy := by
    have hstr : ∀ k : Fin n, isHorizEdge (d k) →
        min ((pos d k).1) ((pos d (k + 1)).1) = vx - 1 → (pos d k).2 ≠ (vy - 1) + 1 := by
      intro k hhk hmk hyk
      rw [show (vy - 1) + 1 = vy from by ring] at hyk
      have hyc := horiz_y_const d hclosed k hhk
      rcases horiz_x_step d hclosed k hhk with hx | hx
      · have hk1 : pos d (k + 1) = pos d (i + 1) := by
          rw [hpe, Prod.ext_iff]; exact ⟨by omega, by rw [hyc]; omega⟩
        have hki : k = i := add_right_cancel (hsimple hk1)
        rw [hki] at hhk; exact not_isHoriz_of_isVert hv hhk
      · have hk0 : pos d k = pos d (i + 1) := by rw [hpe, Prod.ext_iff]; exact ⟨by omega, by omega⟩
        rw [hsimple hk0] at hhk; exact not_isHoriz_of_isVert hvi1 hhk
    have h := rayParity_vstep d (vx - 1) (vy - 1) hstr
    rwa [show vy - 1 + 1 = vy from by ring] at h
  apply cornerWeight_eq_zero_of_two_dvd d hclosed (pos d (i + 1))
  have hz : (cornerCount (interiorCells d hclosed) (pos d (i + 1)) : ℤ)
      = 2 * ((if rayParity d vx vy = 1 then (1 : ℤ) else 0)
        + (if rayParity d (vx - 1) vy = 1 then 1 else 0)) := by
    rw [hpe, cornerCount_interior_eq d hclosed vx vy, hSE, hSW]; ring
  have : (2 : ℤ) ∣ (cornerCount (interiorCells d hclosed) (pos d (i + 1)) : ℤ) := ⟨_, hz⟩
  exact_mod_cast this


theorem cornerWeight_straight (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (i : Fin n) (hstraight : d (i + 1) = d i) :
    cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = 0 := by
  rcases (show isHorizEdge (d i) ∨ isVertEdge (d i) from by
    rcases stepOf_coords (d i) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;>
      simp only [isHorizEdge, isVertEdge, h] <;> tauto) with hh | hv
  · exact cornerWeight_straight_horiz d hclosed hsimple i hstraight hh
  · exact cornerWeight_straight_vert d hclosed hsimple i hstraight hv

end StatMech.Onsager.StraightCorner
