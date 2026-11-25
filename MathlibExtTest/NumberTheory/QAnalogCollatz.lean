/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QAnalogCollatz

/-! # Tests for the q-analog of the Collatz map -/

open MetaMathlibExt PowerSeries

-- For an odd input and equal parameters, the tail is multiplied by the parameter.
example (A V : PowerSeries (ZMod 2)) : qCollatz A A (1 + X * V) = A * V := by
  have hA : A + A = 0 := by
    ext i
    simp [CharTwo.add_self_eq_zero]
  have h : A * (1 + X * V) + A = X * (A * V) := by
    rw [mul_add, mul_one, add_right_comm, hA, zero_add, mul_left_comm]
  simp [qCollatz, h, qShift_X_mul]

-- At the last allowed iterate, a perturbation of zero has a nonzero constant term.
example (n : ℕ) (V : PowerSeries (ZMod 2)) (hV : constantCoeff V ≠ 0) :
    constantCoeff ((qCollatz 1 1)^[n + 1] (X ^ (n + 1) * V)) ≠ 0 := by
  obtain ⟨W, hW, heq⟩ :=
    qCollatz_iterate_add_X_pow_mul 1 1 (by simp) (by simp) n 0 V hV (n + 1) le_rfl
  have h : (qCollatz 1 1)^[n + 1] (X ^ (n + 1) * V) = W := by
    simpa [Function.iterate_fixed (qCollatz_zero 1 1)] using heq
  rwa [h]
