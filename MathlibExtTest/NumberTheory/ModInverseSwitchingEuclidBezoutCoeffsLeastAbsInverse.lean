/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsLeastAbsInverse

/-! # Tests for `MathlibExt.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsLeastAbsInverse` -/

namespace MathlibExtTest.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsLeastAbsInverse

open MathlibExt.NumberTheory.ModInverseSwitchingWanted

-- The Euclidean pair for (3, 2) is (1, -1): 1 * 3 + (-1) * 2 = 1.
example : (1 : ℤ) * 3 + (-1) * 2 = 1 := by
  let r : ℕ → ℕ := fun i => 3 - i
  let s : ℕ → ℤ := fun i => if i = 1 then -1 else 1
  have hseq : IsEuclidSwitchSeq r s 1 := by
    refine ⟨by decide, ?_, ?_, rfl, ?_, rfl, ?_⟩
    · intro i hi
      interval_cases i <;> decide
    · intro i hi
      interval_cases i <;> decide
    · intro i hi hj
      interval_cases i
      exact ⟨1, by decide, rfl⟩
    · intro i hi hj
      interval_cases i
      decide
  have hr0 : r 0 = 3 / Nat.gcd 3 2 := by decide
  have hr1 : r 1 = 2 / Nat.gcd 3 2 := by decide
  have h := euclid_bezout_coeffs_leastAbsInverse 3 2 (by decide) (by decide)
    r s 1 hseq hr0 hr1
  have hs2 : s 2 = 1 := by decide
  have hs1 : s 1 = -1 := by decide
  have hgcd : Nat.gcd 3 2 = 1 := by decide
  rw [hs2, hs1, hgcd] at h
  simpa only [Nat.cast_one, Nat.cast_ofNat] using h.1

-- One is the least absolute inverse of 3 modulo 2.
example : IsLeastAbsInverse 1 3 2 := by
  let r : ℕ → ℕ := fun i => 3 - i
  let s : ℕ → ℤ := fun i => if i = 1 then -1 else 1
  have hseq : IsEuclidSwitchSeq r s 1 := by
    refine ⟨by decide, ?_, ?_, rfl, ?_, rfl, ?_⟩
    · intro i hi
      interval_cases i <;> decide
    · intro i hi
      interval_cases i <;> decide
    · intro i hi hj
      interval_cases i
      exact ⟨1, by decide, rfl⟩
    · intro i hi hj
      interval_cases i
      decide
  have hr0 : r 0 = 3 / Nat.gcd 3 2 := by decide
  have hr1 : r 1 = 2 / Nat.gcd 3 2 := by decide
  have h := euclid_bezout_coeffs_leastAbsInverse 3 2 (by decide) (by decide)
    r s 1 hseq hr0 hr1
  have hs2 : s 2 = 1 := by decide
  have hgcd : Nat.gcd 3 2 = 1 := by decide
  rw [hs2, hgcd] at h
  simpa using h.2.1

-- Negative one is the least absolute inverse of 2 modulo 3.
example : IsLeastAbsInverse (-1) 2 3 := by
  let r : ℕ → ℕ := fun i => 3 - i
  let s : ℕ → ℤ := fun i => if i = 1 then -1 else 1
  have hseq : IsEuclidSwitchSeq r s 1 := by
    refine ⟨by decide, ?_, ?_, rfl, ?_, rfl, ?_⟩
    · intro i hi
      interval_cases i <;> decide
    · intro i hi
      interval_cases i <;> decide
    · intro i hi hj
      interval_cases i
      exact ⟨1, by decide, rfl⟩
    · intro i hi hj
      interval_cases i
      decide
  have hr0 : r 0 = 3 / Nat.gcd 3 2 := by decide
  have hr1 : r 1 = 2 / Nat.gcd 3 2 := by decide
  have h := euclid_bezout_coeffs_leastAbsInverse 3 2 (by decide) (by decide)
    r s 1 hseq hr0 hr1
  have hs1 : s 1 = -1 := by decide
  have hgcd : Nat.gcd 3 2 = 1 := by decide
  rw [hs1, hgcd] at h
  simpa using h.2.2

end MathlibExtTest.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsLeastAbsInverse
