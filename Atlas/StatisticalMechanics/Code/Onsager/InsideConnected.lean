/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.InsideClimb
namespace StatMech.Onsager.InsideConnected
open Finset StatMech.Onsager.BaseCase StatMech.Onsager.WalkCrossing
  StatMech.Onsager.NoDoubleWind StatMech.Onsager.NoDoubleWind2 StatMech.Onsager.JordanParity
  StatMech.Onsager.InsideClimb
variable {n : ℕ} [NeZero n]






























theorem lexmax_corner_cell_inside
    (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    ∃ M : Fin n, d (M - 1) = 1 ∧ d M = 2 ∧
      rayParity d ((pos d M).1 - 1) ((pos d M).2 - 1) = 1 := by
  obtain ⟨M, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun k => toLex (pos d k)) ⟨(0 : Fin n), Finset.mem_univ _⟩
  
  have hsucc := pos_succ d hclosed M
  have hpred := pos_pred d hclosed M
  
  have hout : d M = 2 ∨ d M = 3 := by
    have hcases := stepOf_coords (d M)
    by_contra hcon
    rw [not_or] at hcon
    rcases hcases with ⟨he, hs⟩ | ⟨he, hs⟩ | ⟨he, hs⟩ | ⟨he, hs⟩
    · have : toLex (pos d M) < toLex (pos d (M + 1)) := by
        rw [hsucc, hs]; apply Prod.Lex.lt_iff.2; left; simp
      exact absurd (hmax _ (Finset.mem_univ _)) (not_le.2 this)
    · have : toLex (pos d M) < toLex (pos d (M + 1)) := by
        rw [hsucc, hs]; apply Prod.Lex.lt_iff.2; right; simp
      exact absurd (hmax _ (Finset.mem_univ _)) (not_le.2 this)
    · exact hcon.1 he
    · exact hcon.2 he
  
  have hin : d (M - 1) = 0 ∨ d (M - 1) = 1 := by
    have hcases := stepOf_coords (d (M - 1))
    by_contra hcon
    rw [not_or] at hcon
    rcases hcases with ⟨he, hs⟩ | ⟨he, hs⟩ | ⟨he, hs⟩ | ⟨he, hs⟩
    · exact hcon.1 he
    · exact hcon.2 he
    · have hlt : toLex (pos d M) < toLex (pos d (M - 1)) := by
        have : pos d (M - 1) = pos d M + (1, 0) := by rw [hpred, hs]; ext <;> simp
        rw [this]; apply Prod.Lex.lt_iff.2; left; simp
      exact absurd (hmax _ (Finset.mem_univ _)) (not_le.2 hlt)
    · have hlt : toLex (pos d M) < toLex (pos d (M - 1)) := by
        have : pos d (M - 1) = pos d M + (0, 1) := by rw [hpred, hs]; ext <;> simp
        rw [this]; apply Prod.Lex.lt_iff.2; right; simp
      exact absurd (hmax _ (Finset.mem_univ _)) (not_le.2 hlt)
  
  have hrf := hreflexfree (M - 1)
  rw [sub_add_cancel] at hrf
  have hcorner : d (M - 1) = 1 ∧ d M = 2 := by
    rcases hin with h0 | h1
    · exfalso
      rcases hout with h2 | h3
      · rw [h0, h2] at hrf; rcases hrf with h | h <;> revert h <;> decide
      · rw [h0, h3] at hrf; rcases hrf with h | h <;> revert h <;> decide
    · rcases hout with h2 | h3
      · exact ⟨h1, h2⟩
      · exfalso; rw [h1, h3] at hrf; rcases hrf with h | h <;> revert h <;> decide
  obtain ⟨hInc, hW⟩ := hcorner
  refine ⟨M, hInc, hW, ?_⟩
  
  have hMx : (pos d (M + 1)).1 = (pos d M).1 - 1 := by
    rw [fst_step d hclosed M, hW]; simp [stepOf]; omega
  
  have hset : (Finset.univ.filter
      (fun k : Fin n => isHorizEdge (d k) ∧
        min ((pos d k).1) ((pos d (k + 1)).1) = (pos d M).1 - 1 ∧
        (pos d M).2 - 1 < (pos d k).2)) = {M} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Or.inr hW, by omega, by omega⟩
    · intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨-, hhoriz, hmin, hgt⟩ := hk
      have hky : (pos d (k + 1)).2 = (pos d k).2 := horiz_y_const d hclosed k hhoriz
      rcases hhoriz with hE | hW'
      · 
        have hkx : (pos d (k + 1)).1 = (pos d k).1 + 1 := by
          rw [fst_step d hclosed k, hE]; simp [stepOf]
        have hkx0 : (pos d k).1 = (pos d M).1 - 1 := by omega
        have hkx1 : (pos d (k + 1)).1 = (pos d M).1 := by omega
        have hle := hmax (k + 1) (Finset.mem_univ _)
        rw [Prod.Lex.le_iff] at hle
        simp only [ofLex_toLex] at hle
        have hyle : (pos d (k + 1)).2 ≤ (pos d M).2 := by
          rcases hle with h | h
          · exfalso; rw [hkx1] at h; exact absurd h (lt_irrefl _)
          · exact h.2
        have hyeq : (pos d k).2 = (pos d M).2 := by omega
        have hpeq : pos d (k + 1) = pos d M := by
          apply Prod.ext
          · rw [hkx1]
          · rw [hky, hyeq]
        have hkM : k = M - 1 := eq_sub_of_add_eq (hsimple hpeq)
        rw [hkM] at hE; rw [hInc] at hE
        exact absurd hE (by decide)
      · 
        have hkx : (pos d (k + 1)).1 = (pos d k).1 - 1 := by
          rw [fst_step d hclosed k, hW']; simp [stepOf]; omega
        have hkx0 : (pos d k).1 = (pos d M).1 := by omega
        have hle := hmax k (Finset.mem_univ _)
        rw [Prod.Lex.le_iff] at hle
        simp only [ofLex_toLex] at hle
        have hyle : (pos d k).2 ≤ (pos d M).2 := by
          rcases hle with h | h
          · exfalso; rw [hkx0] at h; exact absurd h (lt_irrefl _)
          · exact h.2
        have hyeq : (pos d k).2 = (pos d M).2 := by omega
        have hpeq : pos d k = pos d M := by
          apply Prod.ext
          · rw [hkx0]
          · rw [hyeq]
        exact hsimple hpeq
  
  unfold rayParity upCross
  rw [hset]
  simp
