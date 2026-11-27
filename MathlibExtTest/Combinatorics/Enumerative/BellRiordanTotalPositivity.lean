/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.PowerSeries.Inverse
import MathlibExt.Combinatorics.Enumerative.BellRiordanTotalPositivity

open MetaMathlibExt PowerSeries

namespace MetaMathlibExt.BellRiordanTest

private theorem constant_pf (p : ℝ) (hp : 0 ≤ p) :
    Matrix.HasNonnegativeMinors (Matrix.lowerToeplitz fun n => coeff n (C p)) := by
  apply (Matrix.hasNonnegativeMinors_iff_isTotallyNonneg _).mpr
  have he : (Matrix.lowerToeplitz fun n => coeff n (C p)) = Matrix.diagonal fun _ : ℕ => p := by
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij, Matrix.diagonal_apply_ne _ hij.ne]
    · simp
    · simp [hij.le, coeff_C, Nat.sub_ne_zero_of_lt hij, Matrix.diagonal_apply_ne _ hij.ne']
  rw [he]
  exact Matrix.IsTotallyNonneg.diagonal fun _ => hp

-- A positive constant series can have any positive real as its leading entry.
example (t : ℝ) (ht : 0 < t) :
    Matrix.HasNonnegativeMinors
      (Matrix.of fun n k : ℕ => coeff n (C t * (X * C t) ^ k)) := by
  let a (j : ℕ) : ℝ := if j = 0 then t else 0
  apply bellRiordan_hasNonnegativeMinors_of_aSequence (C t) (by simpa using ht.ne') a
  · intro n k
    simp only [a, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
      Nat.zero_lt_succ, ite_true, add_zero]
    rw [pow_succ', ← mul_assoc, mul_left_comm (C t) X, mul_assoc, coeff_succ_X_mul,
      mul_assoc, coeff_C_mul]
  · simpa only [a, coeff_C] using constant_pf t ht.le

-- For A(x) = Z(x) = 1 the array is the lower triangle of ones.
-- Its coefficient matrix repeats the first column of the identity.
example : Matrix.HasNonnegativeMinors
    (Matrix.of fun n k : ℕ => if k ≤ n then (1 : ℝ) else 0) := by
  let δ (j : ℕ) : ℝ := if j = 0 then 1 else 0
  apply riordanArray_hasNonnegativeMinors_of_coeffMatrix (a := δ) (z := δ)
  · refine ⟨by simp, by simp, ?_, ?_⟩
    · intro n
      rw [Finset.sum_eq_single 0] <;> simp_all [δ]
    · intro n k
      rw [Finset.sum_eq_single 0] <;> simp_all [δ]
  · have entry (i j : ℕ) : riordanCoeffMatrix δ δ i j = (1 : Matrix ℕ ℕ ℝ) i (j - 1) := by
      cases j with
      | zero => simp [δ, riordanCoeffMatrix, Matrix.one_apply]
      | succ j =>
        simp [δ, riordanCoeffMatrix, Matrix.one_apply, Nat.sub_eq_zero_iff_le]
        split_ifs <;> first | rfl | omega
    intro k r c hr hc
    let col (i : Fin k) := c i - 1
    have hm : Monotone col := fun _ _ h => Nat.sub_le_sub_right (hc.monotone h) 1
    by_cases hinj : Function.Injective col
    · simpa only [Matrix.submatrix, entry, col] using
        (Matrix.IsTotallyNonneg.one (R := ℝ) hr (hm.strictMono_of_injective hinj))
    · obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hinj
      rw [Matrix.det_zero_of_column_eq hne]
      intro t
      simp only [Matrix.submatrix_apply, entry]
      exact congrArg ((1 : Matrix ℕ ℕ ℝ) (r t)) heq

-- With all three parameters zero and P = 1, the recurrence gives the identity array.
example : Matrix.HasNonnegativeMinors (1 : Matrix ℕ ℕ ℝ) := by
  apply bellRiordanArray_hasNonnegativeMinors_of_pf 1 1 (by simp)
    (r := 0) (s := 0) (t := 0) le_rfl le_rfl le_rfl
  · simpa using constant_pf 1 zero_le_one
  · simp
  · refine ⟨by simp, by simp, ?_, ?_⟩
    · intro n
      simp [coeff_one]
    · intro n k
      rw [Finset.sum_eq_single 0] <;> simp_all [coeff_one]
  · simp

-- At a repeated root the numerator is a square. The normalization also allows P(0) = 2.
example (r u : ℝ) (hr : 0 ≤ r) (hu : 0 ≤ u) (R : ℕ → ℕ → ℝ) :
    let A := (C 2 + C u * X) ^ 2 * (C 2 - C r * X)⁻¹
    IsRiordanArrayAZ (fun n => coeff n A) (fun n => coeff (n + 1) A) R →
      Matrix.HasNonnegativeMinors (Matrix.of R) := by
  intro A hR
  apply bellRiordanArray_hasNonnegativeMinors_of_pf (C 2) A (by norm_num)
    (r := r) (s := 2 * u) (t := u ^ 2) hr (by positivity) (sq_nonneg _)
    (constant_pf 2 (by norm_num)) _ hR (by nlinarith)
  dsimp only [A]
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one, map_mul, map_pow, map_ofNat]
  ring

end MetaMathlibExt.BellRiordanTest
