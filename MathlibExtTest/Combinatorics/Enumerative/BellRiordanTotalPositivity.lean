/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.BellRiordanTotalPositivity

open MetaMathlibExt PowerSeries

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
  · apply (Matrix.hasNonnegativeMinors_iff_isTotallyNonneg _).mpr
    have hd : Matrix.lowerToeplitz a = Matrix.diagonal (fun _ : ℕ => t) := by
      ext i j
      rcases lt_trichotomy i j with hij | rfl | hij
      · simp [hij, Matrix.diagonal_apply_ne _ hij.ne]
      · simp [a]
      · simp [Matrix.lowerToeplitz_apply_of_le _ hij.le, a, Nat.sub_ne_zero_of_lt hij,
          Matrix.diagonal_apply_ne _ hij.ne']
    rw [hd]
    exact Matrix.IsTotallyNonneg.diagonal (fun _ => ht.le)

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
