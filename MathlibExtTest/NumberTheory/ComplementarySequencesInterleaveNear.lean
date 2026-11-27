/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.ComplementarySequencesInterleaveNear

/-! # Tests for the close interleaving formula -/

open MetaMathlibExt

-- For squares, the next square is ahead at n = 1 and exactly at the threshold at n = 3.
example : nthNonValue (fun m => m ^ 2) 1 = 2 ∧ nthNonValue (fun m => m ^ 2) 3 = 5 := by
  let α (m : ℕ) : ℝ := (m ^ 2 : ℕ)
  have hgap (m : ℕ) (_ : 1 ≤ m) : m ^ 2 + m ≤ (m + 1) ^ 2 := by nlinarith
  have hα (m : ℕ) (_ : 2 ≤ m) : ((m - 1) ^ 2 : ℕ) ≤ α m ∧ α m ≤ (m ^ 2 : ℕ) := by
    dsimp only [α]
    exact ⟨by exact_mod_cast Nat.pow_le_pow_left (Nat.sub_le m 1) 2, le_rfl⟩
  have hh (n : ℕ) (hn : 1 ≤ n) :
      1 ≤ n.sqrt ∧ α n.sqrt ≤ n ∧ (n : ℝ) < α (n.sqrt + 1) := by
    dsimp only [α]
    exact ⟨Nat.le_sqrt'.mpr (by simpa using hn), by exact_mod_cast Nat.sqrt_le' n,
      by exact_mod_cast Nat.lt_succ_sqrt' n⟩
  have hclose (m : ℕ) (hm : 1 ≤ m) : ((m ^ 2 : ℕ) : ℝ) - α m < m := by
    simpa [α] using (show (0 : ℝ) < m by exact_mod_cast hm)
  have result :=
    nthNonValue_eq_interleave_of_sub_lt (fun m => m ^ 2) (by decide) hgap α hα Nat.sqrt hh hclose
  have hs₁ : Nat.sqrt 1 = 1 := (Nat.eq_sqrt'.mpr ⟨by decide, by decide⟩).symm
  have hs₃ : Nat.sqrt 3 = 1 := (Nat.eq_sqrt'.mpr ⟨by decide, by decide⟩).symm
  constructor
  · rw [result 1 (by decide), hs₁]
    decide
  · rw [result 3 (by decide), hs₃]
    decide
