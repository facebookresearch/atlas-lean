/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Onsager.NoDoubleWind2

namespace StatMech.Onsager.UmlaufsatzStrip

open Finset
open StatMech.Onsager.BaseCase
open StatMech.Onsager.NoDoubleWind
open StatMech.Onsager.NoDoubleWind2

variable {n : ℕ} [NeZero n]






theorem ymax_NW_corner (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    ∃ M : Fin n, d (M - 1) = 1 ∧ d M = 2 ∧
      (∀ j : Fin n, (pos d j).2 ≤ (pos d M).2) ∧
      (∀ j : Fin n, (pos d j).2 = (pos d M).2 → (pos d j).1 ≤ (pos d M).1) := by
  obtain ⟨M, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun k => toLex (((pos d k).2, (pos d k).1) : ℤ ×ₗ ℤ)) ⟨(0 : Fin n), Finset.mem_univ _⟩
  
  have hsucc := pos_succ d hclosed M
  have hpred := pos_pred d hclosed M
  
  have hout : d M = 2 ∨ d M = 3 := by
    have hcases := stepOf_coords (d M)
    by_contra hcon
    rw [not_or] at hcon
    rcases hcases with ⟨he, hs⟩ | ⟨he, hs⟩ | ⟨he, hs⟩ | ⟨he, hs⟩
    · 
      have hy : (pos d (M + 1)).2 = (pos d M).2 := by rw [hsucc, hs]; simp
      have hx : (pos d (M + 1)).1 = (pos d M).1 + 1 := by rw [hsucc, hs]; simp
      have : toLex (((pos d M).2, (pos d M).1) : ℤ ×ₗ ℤ)
          < toLex (((pos d (M + 1)).2, (pos d (M + 1)).1) : ℤ ×ₗ ℤ) := by
        rw [hy, hx]; exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, by omega⟩)
      exact absurd (hmax _ (Finset.mem_univ _)) (not_le.2 this)
    · 
      have hy : (pos d (M + 1)).2 = (pos d M).2 + 1 := by rw [hsucc, hs]; simp
      have : toLex (((pos d M).2, (pos d M).1) : ℤ ×ₗ ℤ)
          < toLex (((pos d (M + 1)).2, (pos d (M + 1)).1) : ℤ ×ₗ ℤ) := by
        rw [hy]; exact Prod.Lex.toLex_lt_toLex.2 (Or.inl (by omega))
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
    · 
      have hpos : pos d (M - 1) = pos d M + (1, 0) := by rw [hpred, hs]; ext <;> simp
      have hy : (pos d (M - 1)).2 = (pos d M).2 := by rw [hpos]; simp
      have hx : (pos d (M - 1)).1 = (pos d M).1 + 1 := by rw [hpos]; simp
      have : toLex (((pos d M).2, (pos d M).1) : ℤ ×ₗ ℤ)
          < toLex (((pos d (M - 1)).2, (pos d (M - 1)).1) : ℤ ×ₗ ℤ) := by
        rw [hy, hx]; exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, by omega⟩)
      exact absurd (hmax _ (Finset.mem_univ _)) (not_le.2 this)
    · 
      have hpos : pos d (M - 1) = pos d M + (0, 1) := by rw [hpred, hs]; ext <;> simp
      have hy : (pos d (M - 1)).2 = (pos d M).2 + 1 := by rw [hpos]; simp
      have : toLex (((pos d M).2, (pos d M).1) : ℤ ×ₗ ℤ)
          < toLex (((pos d (M - 1)).2, (pos d (M - 1)).1) : ℤ ×ₗ ℤ) := by
        rw [hy]; exact Prod.Lex.toLex_lt_toLex.2 (Or.inl (by omega))
      exact absurd (hmax _ (Finset.mem_univ _)) (not_le.2 this)
  
  have hrf := hreflexfree (M - 1)
  rw [sub_add_cancel] at hrf
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · rcases hin with h0 | h1
    · exfalso
      rcases hout with h2 | h3
      · rw [h0, h2] at hrf; rcases hrf with h | h <;> revert h <;> decide
      · rw [h0, h3] at hrf; rcases hrf with h | h <;> revert h <;> decide
    · exact h1
  · rcases hin with h0 | h1
    · exfalso
      rcases hout with h2 | h3
      · rw [h0, h2] at hrf; rcases hrf with h | h <;> revert h <;> decide
      · rw [h0, h3] at hrf; rcases hrf with h | h <;> revert h <;> decide
    · rcases hout with h2 | h3
      · exact h2
      · exfalso; rw [h1, h3] at hrf; rcases hrf with h | h <;> revert h <;> decide
  · intro j
    have hle := Prod.Lex.toLex_le_toLex.1 (hmax j (Finset.mem_univ _))
    omega
  · intro j hj
    have hle := Prod.Lex.toLex_le_toLex.1 (hmax j (Finset.mem_univ _))
    omega





theorem ymin_SE_corner (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    ∃ m : Fin n, d (m - 1) = 3 ∧ d m = 0 ∧
      (∀ j : Fin n, (pos d m).2 ≤ (pos d j).2) := by
  obtain ⟨m, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun k => toLex (((pos d k).2, (pos d k).1) : ℤ ×ₗ ℤ)) ⟨(0 : Fin n), Finset.mem_univ _⟩
  have hsucc := pos_succ d hclosed m
  have hpred := pos_pred d hclosed m
  
  have hout : d m = 0 ∨ d m = 1 := by
    have hcases := stepOf_coords (d m)
    by_contra hcon
    rw [not_or] at hcon
    rcases hcases with ⟨he, hs⟩ | ⟨he, hs⟩ | ⟨he, hs⟩ | ⟨he, hs⟩
    · exact hcon.1 he
    · exact hcon.2 he
    · 
      have hy : (pos d (m + 1)).2 = (pos d m).2 := by rw [hsucc, hs]; simp
      have hx : (pos d (m + 1)).1 = (pos d m).1 - 1 := by rw [hsucc, hs]; simp [sub_eq_add_neg]
      have : toLex (((pos d (m + 1)).2, (pos d (m + 1)).1) : ℤ ×ₗ ℤ)
          < toLex (((pos d m).2, (pos d m).1) : ℤ ×ₗ ℤ) := by
        rw [hy, hx]; exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, by omega⟩)
      exact absurd (hmin _ (Finset.mem_univ _)) (not_le.2 this)
    · 
      have hy : (pos d (m + 1)).2 = (pos d m).2 - 1 := by rw [hsucc, hs]; simp [sub_eq_add_neg]
      have : toLex (((pos d (m + 1)).2, (pos d (m + 1)).1) : ℤ ×ₗ ℤ)
          < toLex (((pos d m).2, (pos d m).1) : ℤ ×ₗ ℤ) := by
        rw [hy]; exact Prod.Lex.toLex_lt_toLex.2 (Or.inl (by omega))
      exact absurd (hmin _ (Finset.mem_univ _)) (not_le.2 this)
  
  have hin : d (m - 1) = 2 ∨ d (m - 1) = 3 := by
    have hcases := stepOf_coords (d (m - 1))
    by_contra hcon
    rw [not_or] at hcon
    rcases hcases with ⟨he, hs⟩ | ⟨he, hs⟩ | ⟨he, hs⟩ | ⟨he, hs⟩
    · 
      have hpos : pos d (m - 1) = pos d m + (-1, 0) := by rw [hpred, hs]; ext <;> simp
      have hy : (pos d (m - 1)).2 = (pos d m).2 := by rw [hpos]; simp
      have hx : (pos d (m - 1)).1 = (pos d m).1 - 1 := by rw [hpos]; simp [sub_eq_add_neg]
      have : toLex (((pos d (m - 1)).2, (pos d (m - 1)).1) : ℤ ×ₗ ℤ)
          < toLex (((pos d m).2, (pos d m).1) : ℤ ×ₗ ℤ) := by
        rw [hy, hx]; exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, by omega⟩)
      exact absurd (hmin _ (Finset.mem_univ _)) (not_le.2 this)
    · 
      have hpos : pos d (m - 1) = pos d m + (0, -1) := by rw [hpred, hs]; ext <;> simp
      have hy : (pos d (m - 1)).2 = (pos d m).2 - 1 := by rw [hpos]; simp [sub_eq_add_neg]
      have : toLex (((pos d (m - 1)).2, (pos d (m - 1)).1) : ℤ ×ₗ ℤ)
          < toLex (((pos d m).2, (pos d m).1) : ℤ ×ₗ ℤ) := by
        rw [hy]; exact Prod.Lex.toLex_lt_toLex.2 (Or.inl (by omega))
      exact absurd (hmin _ (Finset.mem_univ _)) (not_le.2 this)
    · exact hcon.1 he
    · exact hcon.2 he
  
  have hrf := hreflexfree (m - 1)
  rw [sub_add_cancel] at hrf
  refine ⟨m, ?_, ?_, ?_⟩
  · rcases hin with h2 | h3
    · exfalso
      rcases hout with h0 | h1
      · rw [h2, h0] at hrf; rcases hrf with h | h <;> revert h <;> decide
      · rw [h2, h1] at hrf; rcases hrf with h | h <;> revert h <;> decide
    · exact h3
  · rcases hin with h2 | h3
    · exfalso
      rcases hout with h0 | h1
      · rw [h2, h0] at hrf; rcases hrf with h | h <;> revert h <;> decide
      · rw [h2, h1] at hrf; rcases hrf with h | h <;> revert h <;> decide
    · rcases hout with h0 | h1
      · exact h0
      · exfalso; rw [h3, h1] at hrf; rcases hrf with h | h <;> revert h <;> decide
  · intro j
    have hle := Prod.Lex.toLex_le_toLex.1 (hmin j (Finset.mem_univ _))
    omega







theorem nw_corner_neighbours (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    {M : Fin n} (hin : d (M - 1) = 1) (hout : d M = 2) :
    pos d (M - 1) = pos d M + (0, -1) ∧ pos d (M + 1) = pos d M + (-1, 0) := by
  constructor
  · have h := pos_pred d hclosed M
    rw [hin] at h
    
    have hstep : stepOf (1 : Fin 4) = (0, 1) := rfl
    rw [hstep] at h
    rw [h]; ext <;> simp
  · have h := pos_succ d hclosed M
    rw [hout] at h
    have hstep : stepOf (2 : Fin 4) = (-1, 0) := rfl
    rw [hstep] at h; exact h




theorem nw_corners_distinct_pos (d : Fin n → Fin 4) (hsimple : Function.Injective (pos d))
    {i j : Fin n} (hij : i ≠ j)
    (_hi : d i = 1) (_hi2 : d (i + 1) = 2) (_hj : d j = 1) (_hj2 : d (j + 1) = 2) :
    pos d (i + 1) ≠ pos d (j + 1) := by
  intro h
  exact hij (add_right_cancel (hsimple h))
















def TopRowContiguous (d : Fin n → Fin 4) : Prop :=
  ∃ M : Fin n, (∀ j : Fin n, (pos d j).2 ≤ (pos d M).2) ∧
    ∀ a b : Fin n, (pos d a).2 = (pos d M).2 → (pos d b).2 = (pos d M).2 →
      ∀ x : ℤ, (pos d a).1 ≤ x → x ≤ (pos d b).1 →
        ∃ c : Fin n, pos d c = (x, (pos d M).2)

end StatMech.Onsager.UmlaufsatzStrip
