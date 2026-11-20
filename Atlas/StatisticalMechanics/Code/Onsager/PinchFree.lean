/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.EdgeUnique
import Code.Onsager.WalkCellBridge
import Code.Onsager.CellPinch
import Code.Onsager.StraightCorner











namespace StatMech.Onsager.PinchFree

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity StatMech.Onsager.RayFlipV StatMech.Onsager.RayFlipH
  StatMech.Onsager.EdgeUnique StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellPinch StatMech.Onsager.InteriorCells StatMech.Onsager.WalkCellBridge
  StatMech.Onsager.StraightCorner

variable {n : ℕ} [NeZero n]


theorem straddle_nonempty_of_ne (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (a b : ℤ)
    (h : rayParity d a b ≠ rayParity d (a + 1) b) : (straddleSet d a b).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  exact h (rayParity_hstep d hclosed a b (by
    intro k hvk hxk hstr
    have hmem : k ∈ straddleSet d a b := by
      simp only [straddleSet, mem_filter, mem_univ, true_and]
      exact ⟨hvk, hxk, hstr.1, hstr.2⟩
    rw [hemp] at hmem; exact absurd hmem (Finset.notMem_empty k)))


theorem mid_nonempty_of_ne (d : Fin n → Fin 4) (a b : ℤ)
    (h : rayParity d a b ≠ rayParity d a (b + 1)) : (midSet d a (b + 1)).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  exact h (rayParity_vstep d a b (by
    intro k hhk hmk hyk
    have hmem : k ∈ midSet d a (b + 1) := by
      simp only [midSet, mem_filter, mem_univ, true_and]
      exact ⟨hhk, hmk, hyk⟩
    rw [hemp] at hmem; exact absurd hmem (Finset.notMem_empty k)))


theorem pinch_free (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) (v : ℤ × ℤ) :
    ¬ pinchAt (interiorCells d hclosed) v := by
  obtain ⟨vx, vy⟩ := v
  have hmemc : ∀ x y : ℤ, ((x, y) ∈ interiorCells d hclosed) ↔ rayParity d x y = 1 :=
    fun x y => mem_interiorCells d hclosed (x, y)
  intro hp
  simp only [pinchAt, hmemc] at hp
  
  have hNEne : rayParity d (vx - 1) vy ≠ rayParity d vx vy := by
    rcases hp with ⟨g1, _, g3, _⟩ | ⟨g1, _, g3, _⟩
    · intro he; rw [← he] at g1; exact g3 g1
    · intro he; rw [he] at g1; exact g3 g1
  have hSEne : rayParity d vx (vy - 1) ≠ rayParity d vx vy := by
    rcases hp with ⟨g1, _, _, g4⟩ | ⟨_, g2, g3, _⟩
    · intro he; rw [← he] at g1; exact g4 g1
    · intro he; rw [he] at g2; exact g3 g2
  have hSWne : rayParity d (vx - 1) (vy - 1) ≠ rayParity d (vx - 1) vy := by
    rcases hp with ⟨_, g2, g3, _⟩ | ⟨g1, _, _, g4⟩
    · intro he; rw [he] at g2; exact g3 g2
    · intro he; rw [← he] at g1; exact g4 g1
  
  obtain ⟨k1, hk1⟩ := straddle_nonempty_of_ne d hclosed (vx - 1) vy
    (by rw [show (vx - 1) + 1 = vx from by ring]; exact hNEne)
  obtain ⟨k2, hk2⟩ := mid_nonempty_of_ne d vx (vy - 1)
    (by rw [show (vy - 1) + 1 = vy from by ring]; exact hSEne)
  obtain ⟨k3, hk3⟩ := mid_nonempty_of_ne d (vx - 1) (vy - 1)
    (by rw [show (vy - 1) + 1 = vy from by ring]; exact hSWne)
  rw [show (vy - 1) + 1 = vy from by ring] at hk2 hk3
  have hv1 : pos d k1 = (vx, vy) ∨ pos d (k1 + 1) = (vx, vy) := by
    rcases straddleSet_endpoints d hclosed (vx - 1) vy k1 hk1 with ⟨ha, _⟩ | ⟨_, hb⟩
    · left; rw [ha]; exact Prod.ext (by ring) rfl
    · right; rw [hb]; exact Prod.ext (by ring) rfl
  have hv2 : pos d k2 = (vx, vy) ∨ pos d (k2 + 1) = (vx, vy) := by
    rcases midSet_endpoints d hclosed vx vy k2 hk2 with ⟨ha, _⟩ | ⟨_, hb⟩
    · left; rw [ha]
    · right; rw [hb]
  have hv3 : pos d k3 = (vx, vy) ∨ pos d (k3 + 1) = (vx, vy) := by
    rcases midSet_endpoints d hclosed (vx - 1) vy k3 hk3 with ⟨_, hb⟩ | ⟨ha, _⟩
    · right; rw [hb]; exact Prod.ext (by ring) rfl
    · left; rw [ha]; exact Prod.ext (by ring) rfl
  
  obtain ⟨m, hm⟩ : ∃ m, pos d m = (vx, vy) := hv1.elim (fun h => ⟨k1, h⟩) (fun h => ⟨k1 + 1, h⟩)
  have hinc : ∀ k : Fin n, (pos d k = (vx, vy) ∨ pos d (k + 1) = (vx, vy)) → k = m ∨ k = m - 1 := by
    intro k hk
    rcases hk with h | h
    · exact Or.inl (hsimple (h.trans hm.symm))
    · right; have h2 : k + 1 = m := hsimple (h.trans hm.symm); rw [← h2]; abel
  
  have hVk1 : isVertEdge (d k1) := by
    simp only [straddleSet, mem_filter, mem_univ, true_and] at hk1; exact hk1.1
  have hHk2 : isHorizEdge (d k2) := by
    simp only [midSet, mem_filter, mem_univ, true_and] at hk2; exact hk2.1
  have hHk3 : isHorizEdge (d k3) := by
    simp only [midSet, mem_filter, mem_univ, true_and] at hk3; exact hk3.1
  have h12 : k1 ≠ k2 := fun h => not_isVert_of_isHoriz (h ▸ hHk2) hVk1
  have h13 : k1 ≠ k3 := fun h => not_isVert_of_isHoriz (h ▸ hHk3) hVk1
  have h23 : k2 ≠ k3 := by
    intro h
    have e2 : min ((pos d k2).1) ((pos d (k2 + 1)).1) = vx := by
      simp only [midSet, mem_filter, mem_univ, true_and] at hk2; exact hk2.2.1
    have e3 : min ((pos d k3).1) ((pos d (k3 + 1)).1) = vx - 1 := by
      simp only [midSet, mem_filter, mem_univ, true_and] at hk3; exact hk3.2.1
    rw [h] at e2; omega
  
  have hsub : ({k1, k2, k3} : Finset (Fin n)) ⊆ {m, m - 1} := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx ⊢
    rcases hx with h | h | h
    · rw [h]; exact hinc k1 hv1
    · rw [h]; exact hinc k2 hv2
    · rw [h]; exact hinc k3 hv3
  have hcard3 : ({k1, k2, k3} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [mem_insert, mem_singleton]; push_neg; exact ⟨h12, h13⟩),
      Finset.card_insert_of_notMem (by simp only [mem_singleton]; exact h23),
      Finset.card_singleton]
  have hle : ({k1, k2, k3} : Finset (Fin n)).card ≤ ({m, m - 1} : Finset (Fin n)).card :=
    Finset.card_le_card hsub
  have hle2 : ({m, m - 1} : Finset (Fin n)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  omega


theorem pinchCount_eq_zero (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) (hn : 3 ≤ n) :
    pinchCount (interiorCells d hclosed) = 0 := by
  unfold pinchCount
  apply Finset.sum_eq_zero
  intro v _
  unfold pinchW
  rw [if_neg (pinch_free d hclosed hsimple hn v)]

end StatMech.Onsager.PinchFree
