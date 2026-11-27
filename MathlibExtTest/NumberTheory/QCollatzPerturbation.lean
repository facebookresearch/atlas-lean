/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QCollatzPerturbation

/-! # Tests for one-step perturbations of the q-Collatz map -/

open MetaMathlibExt PowerSeries

-- At n = 0 an order-one perturbation to the even input changes the output's constant term.
example : constantCoeff (qCollatz 1 1 X) ≠ constantCoeff (qCollatz 1 1 0) := by
  obtain ⟨W, hW, h⟩ := qCollatz_add_X_pow_mul 1 1 (by simp) (by simp) 0 0 1 (by simp)
  simp only [pow_one, mul_one, zero_add, pow_zero, one_mul] at h
  rw [h, map_add]
  simpa only [ne_eq, add_eq_left] using hW

-- In the odd branch, the order-two perturbation leaves exactly one factor of X.
example : ∃ W : PowerSeries (ZMod 2), constantCoeff W ≠ 0 ∧
    qCollatz (1 + X) 1 (1 + X ^ 2) = qCollatz (1 + X) 1 1 + X * W := by
  simpa only [pow_one, mul_one] using
    qCollatz_add_X_pow_mul (A := 1 + X) (B := 1) (hA := by simp) (hB := by simp)
      (n := 1) (U := 1) (V := 1) (hV := by simp)
