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
