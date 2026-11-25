/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.NatSqrt
import MathlibExt.NumberTheory.ComplementarySequences

/-!
# Tests for complementary sequences
-/

open MetaMathlibExt

-- The identity sequence has empty positive complement.
example (n : ℕ) : nthNonValue id n = 0 := by
  apply Nat.nth_of_forall_not
  intro x _ ⟨hx, h⟩
  exact h x hx rfl

-- Equality at the threshold selects the last missing integer before the tetrahedral number 4.
example : nthNonValue (fun j => j * (j + 1) * (j + 2) / 6) 2 = 3 := by
  have h (j : ℕ) : (3 - 2) * j + 5 - 3 = j + 2 := by omega
  have result := nthNonValue_pyramidal_two_case_le_eight 3 (by decide) (by decide) 2 (by decide)
  change nthNonValue _ 2 = 3 at result
  simpa only [h] using result

-- At k = 8, the cube root changes from one to two just as the complement skips 9.
example : nthNonValue (fun j => j * (j + 1) * (6 * j + 5 - 8) / 6) 7 = 8 :=
  nthNonValue_pyramidal_two_case_le_eight 8 (by decide) (by decide) 7 (by decide)

example : nthNonValue (fun j => j * (j + 1) * (6 * j + 5 - 8) / 6) 8 = 10 :=
  nthNonValue_pyramidal_two_case_le_eight 8 (by decide) (by decide) 8 (by decide)

-- Squares interleave the sequence of squares plus one. Its value at zero is the first
-- missing positive integer. The three indices exercise both equality thresholds and the interior.
example :
    let f := fun m : ℕ => m ^ 2 + 1
    nthNonValue f 1 = 1 ∧ nthNonValue f 7 = 9 ∧ nthNonValue f 8 = 11 := by
  let f (m : ℕ) := m ^ 2 + 1
  let α (m : ℕ) : ℝ := (m ^ 2 : ℕ)
  have hgap (m : ℕ) (_ : 1 ≤ m) : f m + m ≤ f (m + 1) := by
    dsimp [f]
    nlinarith
  have hα (m : ℕ) (hm : 2 ≤ m) : (f (m - 1) : ℝ) ≤ α m ∧ α m ≤ f m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, α, f]
    constructor
    · exact_mod_cast (show k ^ 2 + 1 ≤ (k + 1) ^ 2 by nlinarith)
    · exact_mod_cast Nat.le_succ _
  have hh (n : ℕ) (hn : 1 ≤ n) :
      1 ≤ n.sqrt ∧ α n.sqrt ≤ n ∧ (n : ℝ) < α (n.sqrt + 1) := by
    dsimp only [α]
    exact ⟨Nat.le_sqrt'.mpr (by simpa using hn), by exact_mod_cast Nat.sqrt_le' n,
      by exact_mod_cast Nat.lt_succ_sqrt' n⟩
  have result := nthNonValue_eq_interleave f (by decide) hgap α hα Nat.sqrt hh
  refine ⟨(result 1 (by decide)).trans ?_, (result 7 (by decide)).trans ?_,
    (result 8 (by decide)).trans ?_⟩ <;> norm_num [f]

-- For squares plus one, the count at 1 is zero even though f 0 = 1.
-- At 3 and 4 the count is one. Only at 4 does the candidate hit the next value, 5.
example :
    let f := fun m : ℕ => m ^ 2 + 1
    nthNonValue f 1 = 1 ∧ nthNonValue f 3 = 4 ∧ nthNonValue f 4 = 6 := by
  let f (m : ℕ) := m ^ 2 + 1
  have hgap (m : ℕ) (_ : 1 ≤ m) : f m + m ≤ f (m + 1) := by
    dsimp [f]
    nlinarith
  have result := nthNonValue_eq_one_step f (by decide) hgap
  exact ⟨(result 1 (by decide)).trans (by decide), (result 3 (by decide)).trans (by decide),
    (result 4 (by decide)).trans (by decide)⟩

-- Non-triangular numbers: 2, 4, 5, 7, ... At n = 4 the rounded root of 2n jumps from 2 to 3
-- and the formula skips the triangular number 6.
example : nthNonValue (fun j => j * (j + 1) / 2) 4 = 7 := by
  rw [nthNonValue_triangular_eq_round 4 (by decide)]
  have h : ⌊Real.sqrt (2 * (4 : ℕ)) + 1 / 2⌋₊ = 3 := by
    rw [Nat.floor_eq_iff (by positivity)]
    have hlo : (5 / 2 : ℝ) ≤ Real.sqrt (2 * (4 : ℕ)) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have hhi : Real.sqrt (2 * (4 : ℕ)) < 7 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    constructor <;> push_cast <;> linarith
  rw [h]
