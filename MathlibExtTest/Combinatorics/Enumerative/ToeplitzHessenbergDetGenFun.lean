/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ToeplitzHessenbergDetGenFun
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open MetaMathlibExt

-- The coefficient of `x²` recovers the `2 × 2` determinant `a₁² - a₀ a₂`.
example (a : ℕ → ℚ) : toeplitzHessenbergDet a 2 = a 1 ^ 2 - a 0 * a 2 := by
  have h := congrArg (PowerSeries.coeff 2) (toeplitzHessenbergDet_genFun a)
  simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, toeplitzHessenbergDet_one] at h
  linear_combination h

-- The coefficient of `x³` gives the `3 × 3` determinant that cofactor expansion computes directly.
example (a : ℕ → ℤ) :
    toeplitzHessenbergDet a 3 = a 1 ^ 3 - 2 * a 0 * a 1 * a 2 + a 0 ^ 2 * a 3 := by
  have h := congrArg (PowerSeries.coeff 3) (toeplitzHessenbergDet_genFun a)
  simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, toeplitzHessenbergDet_one,
    toeplitzHessenbergDet_two] at h
  linear_combination h

example (a : ℕ → ℤ) :
    toeplitzHessenbergDet a 3 = a 1 ^ 3 - 2 * a 0 * a 1 * a 2 + a 0 ^ 2 * a 3 := by
  rw [toeplitzHessenbergDet, Matrix.det_fin_three]
  simp
  ring

-- No hypothesis on `a 0` is needed: for `a 0 = 0` the series `H` is `a 1 * x`, and the identity
-- forces `det(0; a_1, …, a_n) = a_1 ^ n`.
example (a : ℕ → ℚ) (h0 : a 0 = 0) (n : ℕ) : toeplitzHessenbergDet a n = a 1 ^ n := by
  induction n with
  | zero => simp [toeplitzHessenbergDet]
  | succ n ih =>
    have h := congrArg (PowerSeries.coeff (n + 1)) (toeplitzHessenbergDet_genFun a)
    rw [map_add, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ'] at h
    rcases n with _ | n
    · simpa [h0] using h
    · simp [h0, Finset.sum_eq_zero, ih] at h
      rw [h]
      ring
