/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.LinearAlgebra.PowerSumMatrixPairTrace

open Finset MathlibExt.LinearAlgebra.PowerSumMatrixWanted

-- The even decomposition of the sum of four squares yields 30.
example : ∑ i ∈ Icc (1 : ℕ) 4, (i : ℝ) ^ 2 = 30 := by
  rw [sum_pow_eq_sum_trace_of_even 4 2 (by decide)]
  norm_num [show Icc 1 (4 / 2) = {1, 2} by decide, Matrix.diagonal_pow, Fin.sum_univ_two,
    Pi.pow_apply]

-- At exponent zero, the one pair contributes the trace of the identity.
example : ∑ i ∈ Icc (1 : ℕ) 2, (i : ℝ) ^ 0 = 2 := by
  rw [sum_pow_eq_sum_trace_of_even 2 0 (by decide)]
  norm_num [show Icc 1 (2 / 2) = {1} by decide, Matrix.trace_one]

-- At n = 0, the matrix sum is empty for any exponent.
example (k : ℕ) : (∑ i ∈ Icc (1 : ℕ) 0, (i : ℝ) ^ k) = 0 := by
  rw [sum_pow_eq_sum_trace_of_even 0 k (by decide)]
  simp
