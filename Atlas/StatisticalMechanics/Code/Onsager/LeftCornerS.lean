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










namespace StatMech.Onsager.LeftCornerS

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity StatMech.Onsager.RayFlipV StatMech.Onsager.RayFlipH
  StatMech.Onsager.EdgeUnique StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.InteriorCells StatMech.Onsager.WalkCellBridge StatMech.Onsager.Orientation

variable {n : ℕ} [NeZero n]

theorem cornerWeight_leftTurn_S (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) (i : Fin n)
    (hei : d i = 2) (he : d (i + 1) = 3) :
    cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1)))
      = if rayParity d (leftCell (d (i + 1)) (pos d (i + 1))).1
              (leftCell (d (i + 1)) (pos d (i + 1))).2 = 1 then (1 : ℤ) else -1 := by
  set vx := (pos d (i + 1)).1 with hvx
  set vy := (pos d (i + 1)).2 with hvy
  have hposi : pos d i = (vx + 1, vy) := by
    have hs := pos_succ d hclosed i
    rw [hei] at hs
    rw [hvx, hvy, hs]; ext <;> simp [stepOf] <;> omega
  have hposi2 : pos d (i + 1 + 1) = (vx, vy - 1) := by
    have := pos_succ d hclosed (i + 1)
    rw [he] at this
    rw [Prod.ext_iff]; constructor <;> simp only [this, hvx, hvy, stepOf, Prod.fst_add,
      Prod.snd_add] <;> omega
  
  have hNW : rayParity d (vx - 1) vy = rayParity d vx vy := by
    have hstr : ∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = (vx - 1) + 1 →
        ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ vy ∧ vy < max ((pos d k).2) ((pos d (k + 1)).2)) := by
      intro k hvk hxk ⟨hmn, hmx⟩
      have hxc := vert_x_const d hclosed k hvk
      rcases vert_y_step d hclosed k hvk with hy | hy
      · have hk0 : pos d k = pos d (i + 1) := by
          rw [Prod.ext_iff]; refine ⟨?_, ?_⟩
          · rw [show (pos d (i + 1)).1 = vx from hvx.symm]; omega
          · rw [show (pos d (i + 1)).2 = vy from hvy.symm]; omega
        have hki : k = i + 1 := hsimple hk0
        have hy2 : (pos d (i + 1 + 1)).2 = vy - 1 := by rw [hposi2]
        rw [hki, hy2, show (pos d (i + 1)).2 = vy from hvy.symm] at hy
        omega
      · have hk1 : pos d (k + 1) = pos d (i + 1) := by
          rw [Prod.ext_iff]; refine ⟨?_, ?_⟩
          · rw [show (pos d (i + 1)).1 = vx from hvx.symm, hxc]; omega
          · rw [show (pos d (i + 1)).2 = vy from hvy.symm]; omega
        have hki : k = i := add_right_cancel (hsimple hk1)
        rw [hki, hei] at hvk; exact absurd hvk (by decide)
    have h := rayParity_hstep d hclosed (vx - 1) vy hstr
    rwa [show vx - 1 + 1 = vx from by ring] at h
  
  have hedgei_mid : i ∈ midSet d vx vy := by
    simp only [midSet, mem_filter, mem_univ, true_and]
    refine ⟨Or.inr hei, ?_, ?_⟩
    · rw [hposi, show (pos d (i + 1)).1 = vx from hvx.symm]; omega
    · rw [hposi]
  have hSE : rayParity d vx (vy - 1) = rayParity d vx vy + 1 := by
    have h := rayParity_vflip d vx (vy - 1)
      (by rw [show vy - 1 + 1 = vy from by ring]
          exact midSet_card_odd_of_mem d hclosed hsimple hn vx vy i hedgei_mid)
    rwa [show vy - 1 + 1 = vy from by ring] at h
  
  have hedgei1_str : i + 1 ∈ straddleSet d (vx - 1) (vy - 1) := by
    simp only [straddleSet, mem_filter, mem_univ, true_and]
    refine ⟨Or.inr he, ?_, ?_, ?_⟩
    · rw [show (pos d (i + 1)).1 = vx from hvx.symm]; omega
    · rw [hposi2, show (pos d (i + 1)).2 = vy from hvy.symm]; simp
    · rw [hposi2, show (pos d (i + 1)).2 = vy from hvy.symm]; simp
  have hSW : rayParity d (vx - 1) (vy - 1) = rayParity d vx (vy - 1) + 1 := by
    have h := rayParity_hflip d hclosed (vx - 1) (vy - 1)
      (straddleSet_card_odd_of_mem d hclosed hsimple hn (vx - 1) (vy - 1) (i + 1) hedgei1_str)
    rwa [show vx - 1 + 1 = vx from by ring] at h
  
  have hcorner : leftCell (d (i + 1)) (pos d (i + 1)) = (vx, vy - 1) := by
    rw [he]; simp only [leftCell]; rw [Prod.ext_iff]; exact ⟨rfl, rfl⟩
  have hpe : pos d (i + 1) = (vx, vy) := Prod.ext hvx.symm hvy.symm
  have hcc : (cornerCount (interiorCells d hclosed) (pos d (i + 1)) : ℤ)
      = (if rayParity d vx vy = 1 then (1 : ℤ) else 0)
        + (if rayParity d (vx - 1) vy = 1 then 1 else 0)
        + (if rayParity d vx (vy - 1) = 1 then 1 else 0)
        + (if rayParity d (vx - 1) (vy - 1) = 1 then 1 else 0) := by
    rw [hpe]; exact cornerCount_interior_eq d hclosed vx vy
  rw [hcorner]
  show cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1)))
      = if rayParity d vx (vy - 1) = 1 then (1 : ℤ) else -1
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d vx vy) with h0 | h1
  · have e1 : rayParity d (vx - 1) vy = 0 := by rw [hNW, h0]
    have e2 : rayParity d vx (vy - 1) = 1 := by rw [hSE, h0]; decide
    have e3 : rayParity d (vx - 1) (vy - 1) = 0 := by rw [hSW, hSE, h0]; decide
    have hccn : cornerCount (interiorCells d hclosed) (pos d (i + 1)) = 1 := by
      have hz : (cornerCount (interiorCells d hclosed) (pos d (i + 1)) : ℤ) = 1 := by
        rw [hcc, h0, e1, e2, e3]
        simp only [if_neg (show ¬((0 : ZMod 2) = 1) from by decide),
          if_pos (show (1 : ZMod 2) = 1 from by decide)]
        norm_num
      exact_mod_cast hz
    rw [hccn, e2]
    simp only [if_pos (show (1 : ZMod 2) = 1 from by decide)]
    decide
  · have e1 : rayParity d (vx - 1) vy = 1 := by rw [hNW, h1]
    have e2 : rayParity d vx (vy - 1) = 0 := by rw [hSE, h1]; decide
    have e3 : rayParity d (vx - 1) (vy - 1) = 1 := by rw [hSW, hSE, h1]; decide
    have hccn : cornerCount (interiorCells d hclosed) (pos d (i + 1)) = 3 := by
      have hz : (cornerCount (interiorCells d hclosed) (pos d (i + 1)) : ℤ) = 3 := by
        rw [hcc, h1, e1, e2, e3]
        simp only [if_neg (show ¬((0 : ZMod 2) = 1) from by decide),
          if_pos (show (1 : ZMod 2) = 1 from by decide)]
        norm_num
      exact_mod_cast hz
    rw [hccn, e2]
    simp only [if_neg (show ¬((0 : ZMod 2) = 1) from by decide)]
    decide

end StatMech.Onsager.LeftCornerS
