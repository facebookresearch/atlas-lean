/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































import Mathlib
import Code.Onsager.BaseCase

namespace StatMech.Onsager.NoDoubleWind

open Finset
open StatMech.Onsager.BaseCase

variable {n : ℕ} [NeZero n]




theorem pos_zero (d : Fin n → Fin 4) : pos d 0 = 0 := by
  have h0 : (Finset.univ.filter (· < (0 : Fin n))) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro i _
    exact Fin.not_lt_zero i
  rw [pos, h0, Finset.sum_empty]


theorem pos_succ (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (k : Fin n) :
    pos d (k + 1) = pos d k + stepOf (d k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  by_cases hk : k = Fin.last m
  · 
    have hzero : (k + 1 : Fin (m + 1)) = 0 := by
      apply Fin.ext
      rw [Fin.val_add_one, if_pos hk]; rfl
    have hfilter : (Finset.univ.filter (· < k)) = Finset.univ.erase k := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      constructor
      · intro hi; exact ne_of_lt hi
      · intro hne
        have hik : i ≤ k := by rw [hk]; exact Fin.le_last i
        exact lt_of_le_of_ne hik hne
    rw [hzero, pos_zero]
    have : pos d k = ∑ i ∈ Finset.univ.erase k, stepOf (d i) := by
      rw [pos, hfilter]
    rw [this, add_comm]
    rw [Finset.add_sum_erase Finset.univ (fun i => stepOf (d i)) (Finset.mem_univ k)]
    exact hclosed.symm
  · 
    have hval : ((k + 1 : Fin (m + 1)) : ℕ) = k.val + 1 := by
      rw [Fin.val_add_one, if_neg hk]
    have hfilter : (Finset.univ.filter (· < (k + 1))) = insert k (Finset.univ.filter (· < k)) := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hi
        rw [Fin.lt_def, hval] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · exact Or.inr (Fin.lt_def.2 h)
        · exact Or.inl (Fin.ext h)
      · intro h
        rw [Fin.lt_def, hval]
        rcases h with heq | hlt
        · rw [heq]; exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (Fin.lt_def.1 hlt)
    have hnotmem : k ∉ Finset.univ.filter (· < k) := by
      simp [Finset.mem_filter]
    rw [pos, hfilter, Finset.sum_insert hnotmem, add_comm]
    rfl


theorem pos_pred (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (M : Fin n) :
    pos d M = pos d (M - 1) + stepOf (d (M - 1)) := by
  have h := pos_succ d hclosed (M - 1)
  rwa [sub_add_cancel] at h




theorem stepOf_coords (w : Fin 4) :
    (w = 0 ∧ stepOf w = (1, 0)) ∨ (w = 1 ∧ stepOf w = (0, 1)) ∨
    (w = 2 ∧ stepOf w = (-1, 0)) ∨ (w = 3 ∧ stepOf w = (0, -1)) := by
  fin_cases w <;> simp [stepOf]




theorem lexmax_corner (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    ∃ M : Fin n, d (M - 1) = 1 ∧ d M = 2 := by
  obtain ⟨M, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun k => toLex (pos d k))
    ⟨(0 : Fin n), Finset.mem_univ _⟩
  refine ⟨M, ?_⟩
  
  have hsucc := pos_succ d hclosed M
  have hpred := pos_pred d hclosed M
  
  have hout : d M = 2 ∨ d M = 3 := by
    have hcases := stepOf_coords (d M)
    by_contra hcon
    rw [not_or] at hcon
    rcases hcases with ⟨he, hs⟩ | ⟨he, hs⟩ | ⟨he, hs⟩ | ⟨he, hs⟩
    · 
      have : toLex (pos d M) < toLex (pos d (M + 1)) := by
        rw [hsucc, hs]; apply Prod.Lex.lt_iff.2; left; simp
      exact absurd (hmax _ (Finset.mem_univ _)) (not_le.2 this)
    · 
      have : toLex (pos d M) < toLex (pos d (M + 1)) := by
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
    · 
      have hlt : toLex (pos d M) < toLex (pos d (M - 1)) := by
        have : pos d (M - 1) = pos d M + (1, 0) := by rw [hpred, hs]; ext <;> simp
        rw [this]; apply Prod.Lex.lt_iff.2; left; simp
      exact absurd (hmax _ (Finset.mem_univ _)) (not_le.2 hlt)
    · 
      have hlt : toLex (pos d M) < toLex (pos d (M - 1)) := by
        have : pos d (M - 1) = pos d M + (0, 1) := by rw [hpred, hs]; ext <;> simp
        rw [this]; apply Prod.Lex.lt_iff.2; right; simp
      exact absurd (hmax _ (Finset.mem_univ _)) (not_le.2 hlt)
  
  have hrf := hreflexfree (M - 1)
  rw [sub_add_cancel] at hrf
  rcases hin with h0 | h1
  · exfalso
    rcases hout with h2 | h3
    · rw [h0, h2] at hrf; rcases hrf with h | h <;> revert h <;> decide
    · rw [h0, h3] at hrf; rcases hrf with h | h <;> revert h <;> decide
  · rcases hout with h2 | h3
    · exact ⟨h1, h2⟩
    · exfalso; rw [h1, h3] at hrf; rcases hrf with h | h <;> revert h <;> decide

end StatMech.Onsager.NoDoubleWind
