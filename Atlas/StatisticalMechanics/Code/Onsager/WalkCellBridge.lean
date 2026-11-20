/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.InteriorCells
import Code.Onsager.CellConnect










namespace StatMech.Onsager.WalkCellBridge

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.CellCount StatMech.Onsager.CellEuler StatMech.Onsager.CellConnect
  StatMech.Onsager.JordanParity StatMech.Onsager.InteriorCells

variable {n : ℕ} [NeZero n]



theorem cornerCount_interior_eq (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (vx vy : ℤ) :
    (cornerCount (interiorCells d hclosed) (vx, vy) : ℤ)
      = (if rayParity d vx vy = 1 then (1 : ℤ) else 0)
        + (if rayParity d (vx - 1) vy = 1 then 1 else 0)
        + (if rayParity d vx (vy - 1) = 1 then 1 else 0)
        + (if rayParity d (vx - 1) (vy - 1) = 1 then 1 else 0) := by
  have hset : (({(vx, vy), ((vx, vy).1 - 1, (vx, vy).2), ((vx, vy).1, (vx, vy).2 - 1),
        ((vx, vy).1 - 1, (vx, vy).2 - 1)}) : Finset (ℤ × ℤ))
      = {(vx, vy), (vx - 1, vy), (vx, vy - 1), (vx - 1, vy - 1)} := rfl
  rw [cornerCount_eq_inter, hset, card_inter_eq_sum,
      Finset.sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_insert (by simp only [mem_singleton, Prod.mk.injEq]; omega),
      Finset.sum_singleton]
  simp only [mem_interiorCells]
  ring

open StatMech.Onsager.WalkCrossing




theorem rayParity_const_of_not_vertex (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (vx vy : ℤ) (hv : ∀ k : Fin n, pos d k ≠ (vx, vy)) :
    rayParity d (vx - 1) vy = rayParity d vx vy
      ∧ rayParity d vx (vy - 1) = rayParity d vx vy
      ∧ rayParity d (vx - 1) (vy - 1) = rayParity d vx vy := by
  
  have hstr1 : ∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = (vx - 1) + 1 →
      ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ vy ∧ vy < max ((pos d k).2) ((pos d (k + 1)).2)) := by
    intro k hvk hx ⟨hmn, hmx⟩
    have hxc := vert_x_const d hclosed k hvk
    rcases vert_y_step d hclosed k hvk with h | h
    · exact hv k (Prod.ext (by rw [hx]; ring) (by omega))
    · exact hv (k + 1) (Prod.ext (by rw [hxc, hx]; ring) (by omega))
  have e1 : rayParity d (vx - 1) vy = rayParity d vx vy := by
    have := rayParity_hstep d hclosed (vx - 1) vy hstr1
    rwa [show vx - 1 + 1 = vx from by ring] at this
  
  have hstr2 : ∀ k : Fin n, isHorizEdge (d k) → min ((pos d k).1) ((pos d (k + 1)).1) = vx →
      (pos d k).2 ≠ (vy - 1) + 1 := by
    intro k hhk hx hy
    have hyc := horiz_y_const d hclosed k hhk
    rcases horiz_x_step d hclosed k hhk with h | h
    · exact hv k (Prod.ext (by omega) (by omega))
    · exact hv (k + 1) (Prod.ext (by omega) (by omega))
  have e2 : rayParity d vx (vy - 1) = rayParity d vx vy := by
    have := rayParity_vstep d vx (vy - 1) hstr2
    rwa [show vy - 1 + 1 = vy from by ring] at this
  
  have hstr3 : ∀ k : Fin n, isHorizEdge (d k) → min ((pos d k).1) ((pos d (k + 1)).1) = vx - 1 →
      (pos d k).2 ≠ (vy - 1) + 1 := by
    intro k hhk hx hy
    have hyc := horiz_y_const d hclosed k hhk
    rcases horiz_x_step d hclosed k hhk with h | h
    · exact hv (k + 1) (Prod.ext (by omega) (by omega))
    · exact hv k (Prod.ext (by omega) (by omega))
  have e3 : rayParity d (vx - 1) (vy - 1) = rayParity d (vx - 1) vy := by
    have := rayParity_vstep d (vx - 1) (vy - 1) hstr3
    rwa [show vy - 1 + 1 = vy from by ring] at this
  exact ⟨e1, e2, e3.trans e1⟩

end StatMech.Onsager.WalkCellBridge
