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











namespace StatMech.Onsager.LeftCornerN

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity StatMech.Onsager.RayFlipV StatMech.Onsager.RayFlipH
  StatMech.Onsager.EdgeUnique StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.InteriorCells StatMech.Onsager.WalkCellBridge StatMech.Onsager.Orientation

variable {n : ℕ} [NeZero n]

theorem cornerWeight_leftTurn_N (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) (i : Fin n)
    (hei : d i = 0) (he : d (i + 1) = 1) :
    cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1)))
      = if rayParity d (leftCell (d (i + 1)) (pos d (i + 1))).1
              (leftCell (d (i + 1)) (pos d (i + 1))).2 = 1 then (1 : ℤ) else -1 := by
  set vx := (pos d (i + 1)).1 with hvx
  set vy := (pos d (i + 1)).2 with hvy
  
  have hposi : pos d i = (vx - 1, vy) := by
    have := pos_succ d hclosed i
    rw [hei] at this
    have h1 : (pos d (i + 1)).1 = (pos d i).1 + 1 := by rw [this]; simp [stepOf]
    have h2 : (pos d (i + 1)).2 = (pos d i).2 := by rw [this]; simp [stepOf]
    rw [Prod.ext_iff]; constructor <;> simp only [hvx, hvy] <;> omega
  have hposi2 : pos d (i + 1 + 1) = (vx, vy + 1) := by
    have := pos_succ d hclosed (i + 1)
    rw [he] at this
    rw [Prod.ext_iff]; constructor <;> simp only [this, hvx, hvy, stepOf, Prod.fst_add,
      Prod.snd_add] <;> omega
  
  have hedgei_mid : i ∈ midSet d (vx - 1) vy := by
    simp only [midSet, mem_filter, mem_univ, true_and]
    refine ⟨Or.inl hei, ?_, ?_⟩
    · rw [hposi]; simp only []; rw [show (pos d (i + 1)).1 = vx from hvx.symm]; omega
    · rw [hposi]
  have hSW : rayParity d (vx - 1) (vy - 1) = rayParity d (vx - 1) vy + 1 := by
    have h := rayParity_vflip d (vx - 1) (vy - 1)
      (by rw [show vy - 1 + 1 = vy from by ring]
          exact midSet_card_odd_of_mem d hclosed hsimple hn (vx - 1) vy i hedgei_mid)
    rwa [show vy - 1 + 1 = vy from by ring] at h
  
  have hedgei1_str : i + 1 ∈ straddleSet d (vx - 1) vy := by
    simp only [straddleSet, mem_filter, mem_univ, true_and]
    refine ⟨Or.inl he, ?_, ?_, ?_⟩
    · rw [show (pos d (i + 1)).1 = vx from hvx.symm]; omega
    · rw [hposi2, show (pos d (i + 1)).2 = vy from hvy.symm]; simp
    · rw [hposi2, show (pos d (i + 1)).2 = vy from hvy.symm]; simp
  have hNE : rayParity d (vx - 1) vy = rayParity d vx vy + 1 := by
    have h := rayParity_hflip d hclosed (vx - 1) vy
      (straddleSet_card_odd_of_mem d hclosed hsimple hn (vx - 1) vy (i + 1) hedgei1_str)
    rwa [show vx - 1 + 1 = vx from by ring] at h
  
  have hSE : rayParity d vx (vy - 1) = rayParity d vx vy := by
    have hstr : ∀ k : Fin n, isHorizEdge (d k) →
        min ((pos d k).1) ((pos d (k + 1)).1) = vx → (pos d k).2 ≠ (vy - 1) + 1 := by
      intro k hhk hmk hyk
      rw [show (vy - 1) + 1 = vy from by ring] at hyk
      
      have hyc := horiz_y_const d hclosed k hhk
      rcases horiz_x_step d hclosed k hhk with hx | hx
      · 
        have : pos d k = pos d (i + 1) := by
          rw [Prod.ext_iff]; refine ⟨?_, ?_⟩
          · rw [show (pos d (i + 1)).1 = vx from hvx.symm]; omega
          · rw [show (pos d (i + 1)).2 = vy from hvy.symm]; exact hyk
        rw [hsimple this, he] at hhk; exact absurd hhk (by decide)
      · 
        have hk1 : pos d (k + 1) = pos d (i + 1) := by
          rw [Prod.ext_iff]; refine ⟨?_, ?_⟩
          · rw [show (pos d (i + 1)).1 = vx from hvx.symm]; omega
          · rw [show (pos d (i + 1)).2 = vy from hvy.symm]; rw [hyc]; exact hyk
        have hki : k = i := by
          have := hsimple hk1; exact add_right_cancel this
        rw [hki, hposi] at hmk
        rw [show (pos d (i + 1)).1 = vx from hvx.symm] at hmk
        simp only at hmk; omega
    have h := rayParity_vstep d vx (vy - 1) hstr
    rwa [show vy - 1 + 1 = vy from by ring] at h
  
  have hNW : (leftCell (d (i + 1)) (pos d (i + 1))) = (vx - 1, vy) := by
    rw [he]; simp only [leftCell]; rw [Prod.ext_iff]; exact ⟨rfl, rfl⟩
  
  have hpe : pos d (i + 1) = (vx, vy) := Prod.ext hvx.symm hvy.symm
  have hcc : (cornerCount (interiorCells d hclosed) (pos d (i + 1)) : ℤ)
      = (if rayParity d vx vy = 1 then (1 : ℤ) else 0)
        + (if rayParity d (vx - 1) vy = 1 then 1 else 0)
        + (if rayParity d vx (vy - 1) = 1 then 1 else 0)
        + (if rayParity d (vx - 1) (vy - 1) = 1 then 1 else 0) := by
    rw [hpe]; exact cornerCount_interior_eq d hclosed vx vy
  rw [hNW]
  show cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1)))
      = if rayParity d (vx - 1) vy = 1 then (1 : ℤ) else -1
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (rayParity d vx vy) with h0 | h1
  · have e1 : rayParity d (vx - 1) vy = 1 := by rw [hNE, h0]; decide
    have e2 : rayParity d vx (vy - 1) = 0 := by rw [hSE, h0]
    have e3 : rayParity d (vx - 1) (vy - 1) = 0 := by rw [hSW, hNE, h0]; decide
    have hccn : cornerCount (interiorCells d hclosed) (pos d (i + 1)) = 1 := by
      have hz : (cornerCount (interiorCells d hclosed) (pos d (i + 1)) : ℤ) = 1 := by
        rw [hcc, h0, e1, e2, e3]
        simp only [if_neg (show ¬((0 : ZMod 2) = 1) from by decide),
          if_pos (show (1 : ZMod 2) = 1 from by decide)]
        norm_num
      exact_mod_cast hz
    rw [hccn, e1]
    simp only [if_pos (show (1 : ZMod 2) = 1 from by decide)]
    decide
  · have e1 : rayParity d (vx - 1) vy = 0 := by rw [hNE, h1]; decide
    have e2 : rayParity d vx (vy - 1) = 1 := by rw [hSE, h1]
    have e3 : rayParity d (vx - 1) (vy - 1) = 1 := by rw [hSW, hNE, h1]; decide
    have hccn : cornerCount (interiorCells d hclosed) (pos d (i + 1)) = 3 := by
      have hz : (cornerCount (interiorCells d hclosed) (pos d (i + 1)) : ℤ) = 3 := by
        rw [hcc, h1, e1, e2, e3]
        simp only [if_neg (show ¬((0 : ZMod 2) = 1) from by decide),
          if_pos (show (1 : ZMod 2) = 1 from by decide)]
        norm_num
      exact_mod_cast hz
    rw [hccn, e1]
    simp only [if_neg (show ¬((0 : ZMod 2) = 1) from by decide)]
    decide

end StatMech.Onsager.LeftCornerN
