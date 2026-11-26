/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.ModInverseSwitching

open MathlibExt.NumberTheory.ModInverseSwitchingWanted

-- The negative Bézout coefficient -2 represents the inverse of 7 modulo 5.
example : (-2 : ℤ) * 7 ≡ 1 [ZMOD 5] ∧ (3 : ℤ) * 5 ≡ 1 [ZMOD 7] :=
  bezout_coeffs_are_inverses 7 5 (by decide) (by decide) (by decide) (-2) 3 (by decide)

-- A zero coefficient can represent an inverse modulo one.
example : (0 : ℤ) * 4 ≡ 1 [ZMOD 1] ∧ (1 : ℤ) * 1 ≡ 1 [ZMOD 4] :=
  bezout_coeffs_are_inverses 4 1 (by decide) (by decide) (by decide) 0 1 (by decide)

-- A negative representative of 3 modulo 5 gives a switching pair.
example : ∃ x y : ℤ, x * (-2) ≡ 1 [ZMOD 5] ∧ y * 5 ≡ 1 [ZMOD 3] ∧ x * 3 + y * 5 = 1 :=
  (exists_eq_mul_add_iff_switching 3 5 (by decide) (by decide) (-2) (by decide) (by decide)).mp
    ⟨1, by decide⟩

-- The switching pair (-2, 1) for 2 and 5 recovers a negative quotient when t = 7.
example : ∃ k : ℤ, 2 = k * 5 + 7 :=
  (exists_eq_mul_add_iff_switching 2 5 (by decide) (by decide) 7 (by decide) (by decide)).mpr
    ⟨-2, 1, by decide, by decide, by decide⟩

-- With n = 1 the representative t = 0 is allowed.
example : ∃ x y : ℤ, x * 0 ≡ 1 [ZMOD 1] ∧ y * 1 ≡ 1 [ZMOD 3] ∧ x * 3 + y * 1 = 1 :=
  (exists_eq_mul_add_iff_switching 3 1 (by decide) (by decide) 0 (by decide) (by decide)).mp
    ⟨3, by decide⟩

-- For modulus two, only the positive endpoint is a least absolute inverse.
example : IsLeastAbsInverse 1 1 2 ∧ ¬ IsLeastAbsInverse (-1) 1 2 := by
  unfold IsLeastAbsInverse
  decide

-- Both inverses are extremal for the Euclidean sequence starting with 3 and 2.
example : IsLeastAbsInverse (-1) 2 3 ∧ 2 * |(-1 : ℤ)| = 3 - 1 ∧ 2 * |(1 : ℤ)| = 2 := by
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
  have h : IsLeastAbsInverse (s 2) (r 2 : ℤ) (r 1) := by
    unfold IsLeastAbsInverse
    decide
  exact ⟨isLeastAbsInverse_succ_imp r s 1 hseq 1 le_rfl le_rfl h,
    (abs_eq_halves_iff_eq_two_of_odd_even r s 1 hseq (by decide) (by decide)).mpr rfl⟩

-- A switching sequence requires at least one Euclidean division.
example (r : ℕ → ℕ) (s : ℕ → ℤ) : ¬ IsEuclidSwitchSeq r s 0 :=
  fun h => (Nat.lt_irrefl 0) h.1

-- For remainders 8, 3, 2, 1 the second inverse is -1, attaining its odd-modulus bound.
example : 2 * |(3 : ℤ)| < 8 := by
  let r : ℕ → ℕ
    | 0 => 8
    | 1 => 3
    | 2 => 2
    | _ => 1
  let s : ℕ → ℤ
    | 1 => 3
    | 2 => -1
    | _ => 1
  have hseq : IsEuclidSwitchSeq r s 2 := by
    refine ⟨by decide, ?_, ?_, rfl, ?_, rfl, ?_⟩
    · intro i hi
      interval_cases i <;> decide
    · intro i hi
      interval_cases i <;> decide
    · intro i hi hj
      interval_cases i
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
    · intro i hi hj
      interval_cases i <;> decide
  exact (abs_lt_of_even_odd r s 2 hseq (by decide) (by decide)).resolve_right (by decide)

-- With remainders 5, 4, 1 the first two inverses cannot both be extremal.
example : ¬ (2 * |(-1 : ℤ)| = 5 - 1 ∧ 2 * |(1 : ℤ)| = 4) := by
  let r : ℕ → ℕ
    | 0 => 5
    | 1 => 4
    | _ => 1
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
  exact mt (abs_eq_halves_iff_eq_two_of_odd_even r s 1 hseq (by decide) (by decide)).mp
    (by decide)
