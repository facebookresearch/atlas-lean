/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Sequences.SymmetricUnimodalProducts
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.IntervalCases

open Polynomial MathlibExt.Combinatorics.Sequences.Unimodal
open MathlibExt.Combinatorics.Sequences.UnimodalProductsWanted

-- A zero polynomial may have a positive chosen bound, even when the other bound is zero.
example : (∀ i, 0 ≤ ((0 : ℝ[X]) * 1).coeff i) ∧
    (∀ i ≤ 4, ((0 : ℝ[X]) * 1).coeff i = ((0 : ℝ[X]) * 1).coeff (4 - i)) ∧
    IsUnimodal ((0 : ℝ[X]) * 1).coeff 4 := by
  simpa only [Nat.add_zero] using
    symmetric_unimodal_mul (P := 0) (Q := 1) (m := 4) (n := 0)
      (hPm := by simp) (hQn := by simp)
      (hPnn := by simp) (hQnn := by intro i; simp only [coeff_one]; split_ifs <;> norm_num)
      (hPsymm := by simp) (hQsymm := by
        intro i hi
        rw [show i = 0 by omega, Nat.sub_zero])
      (hPuni := ⟨0, by omega, fun i hi => by omega, by simp⟩)
      (hQuni := ⟨0, by omega, fun i hi => by omega, fun i _ hi => by omega⟩)

private noncomputable def p : ℝ[X] := monomial 1 1 + monomial 2 1

private noncomputable def q : ℝ[X] :=
  monomial 0 1 + monomial 1 1 + monomial 2 1 + monomial 3 1 + monomial 4 1

private lemma p_coeff (i : ℕ) : p.coeff i =
    (if 1 = i then 1 else 0) + (if 2 = i then 1 else 0) := by
  simp only [p, coeff_add, coeff_monomial_apply]

private lemma q_coeff (i : ℕ) : q.coeff i =
    (if 0 = i then 1 else 0) + (if 1 = i then 1 else 0) + (if 2 = i then 1 else 0) +
    (if 3 = i then 1 else 0) + (if 4 = i then 1 else 0) := by
  simp only [q, coeff_add, coeff_monomial_apply]

-- The factors have unequal actual degrees, and p is padded to degree bound 3.
-- Their product is symmetric and unimodal on the full range 0 through 7.
example : (∀ i, 0 ≤ (p * q).coeff i) ∧
    (∀ i ≤ 7, (p * q).coeff i = (p * q).coeff (7 - i)) ∧
    IsUnimodal (p * q).coeff 7 := by
  apply symmetric_unimodal_mul (m := 3) (n := 4)
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    simp [p_coeff, show 1 ≠ i by omega, show 2 ≠ i by omega]
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    simp [q_coeff, show 0 ≠ i by omega, show 1 ≠ i by omega, show 2 ≠ i by omega,
      show 3 ≠ i by omega, show 4 ≠ i by omega]
  · intro i
    rw [p_coeff]
    split_ifs <;> norm_num
  · intro i
    rw [q_coeff]
    split_ifs <;> norm_num
  · intro i hi
    interval_cases i <;> norm_num [p_coeff]
  · intro i hi
    interval_cases i <;> norm_num [q_coeff]
  · refine ⟨1, by omega, fun i hi => ?_, fun i hi hj => ?_⟩ <;>
      interval_cases i <;> norm_num [p_coeff]
  · refine ⟨2, by omega, fun i hi => ?_, fun i hi hj => ?_⟩ <;>
      interval_cases i <;> norm_num [q_coeff]
