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

-- The second count is unchanged at n = 2 and n = 4, but grows at n = 5 and n = 10.
-- At n = 2 the count is zero despite f 0 = 2; at n = 5 the next value hits the cutoff exactly.
example :
    let f := fun m : ℕ => m ^ 2 + 2
    nthNonValue f 2 = 2 ∧ nthNonValue f 4 = 5 ∧ nthNonValue f 5 = 7 ∧ nthNonValue f 10 = 13 := by
  let f (m : ℕ) := m ^ 2 + 2
  have hgap (m : ℕ) (_ : 1 ≤ m) : f m + m ≤ f (m + 1) := by
    dsimp [f]
    nlinarith
  have result := nthNonValue_eq_two_step f (by decide) hgap
  exact ⟨(result 2 (by decide)).trans (by decide), (result 4 (by decide)).trans (by decide),
    (result 5 (by decide)).trans (by decide), (result 10 (by decide)).trans (by decide)⟩

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

-- The indexing starts at 1, and the first positive nonsquare is 2.
example : nthNonValue (fun j => j ^ 2) 1 = 2 := by
  rw [nthNonValue_sq_eq_round 1 (by decide)]
  have h : ⌊Real.sqrt (1 : ℕ) + 1 / 2⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by positivity)]
    norm_num
  rw [h]

-- The rounded root jumps from 2 to 3 between n = 6 and n = 7, so the sequence skips 9.
example : nthNonValue (fun j => j ^ 2) 6 = 8 := by
  rw [nthNonValue_sq_eq_round 6 (by decide)]
  have h : ⌊Real.sqrt (6 : ℕ) + 1 / 2⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by positivity)]
    have hlo : (3 / 2 : ℝ) ≤ Real.sqrt (6 : ℕ) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have hhi : Real.sqrt (6 : ℕ) < 5 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    constructor <;> push_cast <;> linarith
  rw [h]

example : nthNonValue (fun j => j ^ 2) 7 = 10 := by
  rw [nthNonValue_sq_eq_round 7 (by decide)]
  have h : ⌊Real.sqrt (7 : ℕ) + 1 / 2⌋₊ = 3 := by
    rw [Nat.floor_eq_iff (by positivity)]
    have hlo : (5 / 2 : ℝ) ≤ Real.sqrt (7 : ℕ) :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have hhi : Real.sqrt (7 : ℕ) < 7 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    constructor <;> push_cast <;> linarith
  rw [h]

-- For the shifted sums of squares, the first positive non-value is 1. At n = 5 the
-- condition is an equality and gives 6; at n = 6 it is false and the complement skips 7.
example : nthNonValue (fun j => j + ∑ i ∈ Finset.Icc 1 j, i ^ 2) 1 = 1 :=
  (nthNonValue_add_sumPow 2 (by decide) 1 (by decide)).trans (by decide)

example : nthNonValue (fun j => j + ∑ i ∈ Finset.Icc 1 j, i ^ 2) 5 = 6 :=
  (nthNonValue_add_sumPow 2 (by decide) 5 (by decide)).trans (by decide)

example : nthNonValue (fun j => j + ∑ i ∈ Finset.Icc 1 j, i ^ 2) 6 = 8 :=
  (nthNonValue_add_sumPow 2 (by decide) 6 (by decide)).trans (by decide)

-- For cubes and n = 4, (k + 1) * n is exactly 2^4.
example : nthNonValue (fun j => j + ∑ i ∈ Finset.Icc 1 j, i ^ 3) 4 = 5 :=
  (nthNonValue_add_sumPow 3 (by decide) 4 (by decide)).trans (by decide)

private def pentagonal (j : ℕ) : ℕ := (5 - 2) * j * (j - 1) / 2 + j

-- Since pentagonal j ≥ j, indices above 6 cannot contribute values in this interval.
example : Finset.Icc 1 6 \ (Finset.Icc 1 6).image pentagonal = {2, 3, 4, 6} := by decide

-- Independently compute the non-values using the finite counting formula, not the square root.
example : nthNonValue pentagonal 1 = 2 ∧ nthNonValue pentagonal 3 = 4 ∧
    nthNonValue pentagonal 4 = 6 := by
  have hgap (j : ℕ) (hj : 1 ≤ j) : pentagonal j + j ≤ pentagonal (j + 1) := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [pentagonal, show 5 - 2 = 3 by decide, Nat.add_sub_cancel]
    rw [show 3 * (i + 1 + 1) * (i + 1) = 3 * (i + 1) * i + 6 * (i + 1) by ring]
    omega
  have h := nthNonValue_eq_one_step pentagonal (by decide) hgap
  exact ⟨(h 1 (by decide)).trans (by decide), (h 3 (by decide)).trans (by decide),
    (h 4 (by decide)).trans (by decide)⟩

-- The formula covers a zero square root, equality at the threshold, and a strict crossing at s = 1.
example : nthNonValue pentagonal 1 = 2 ∧ nthNonValue pentagonal 3 = 4 ∧
    nthNonValue pentagonal 4 = 6 := by
  have h := nthNonValue_polygonal 5 (by decide)
  exact ⟨(h 1 (by decide)).trans (by norm_num), (h 3 (by decide)).trans (by norm_num),
    (h 4 (by decide)).trans (by norm_num)⟩
