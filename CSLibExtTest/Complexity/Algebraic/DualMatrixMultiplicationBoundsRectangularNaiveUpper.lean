/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Complexity.Algebraic.DualMatrixMultiplicationBoundsRectangularNaiveUpper
import Mathlib.Algebra.Field.ZMod

/-! # Naive rectangular upper bound tests -/

namespace CSLibExtTest.Complexity.Algebraic.DualMatrixMultiplicationBoundsRectangularNaiveUpper

open Cslib.Complexity.Algebraic
open Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

example : rectangularCircuitExponent ℚ 1 ≤ ENNReal.ofReal 3 := by
  have h := rectangularNaiveUpper ℚ 1 zero_le_one
  rw [show (2 : ℝ) + 1 = 3 by norm_num] at h
  exact h

example : rectangularCircuitExponent ℚ 2 ≤ ENNReal.ofReal 4 := by
  have h := rectangularNaiveUpper ℚ 2 (by norm_num)
  rw [show (2 : ℝ) + 2 = 4 by norm_num] at h
  exact h

example : rectangularCircuitExponent ℚ (1 / 2) ≤ ENNReal.ofReal (5 / 2) := by
  have h := rectangularNaiveUpper ℚ (1 / 2) (by norm_num)
  rw [show (2 : ℝ) + 1 / 2 = 5 / 2 by norm_num] at h
  exact h

example : rectangularCircuitExponent (ZMod 2) 1 ≤ ENNReal.ofReal 3 := by
  have h := rectangularNaiveUpper (ZMod 2) 1 zero_le_one
  rw [show (2 : ℝ) + 1 = 3 by norm_num] at h
  exact h

example : squareMatrixMultiplicationCircuitExponent ℚ ≤ ENNReal.ofReal 3 := by
  rw [squareMatrixMultiplicationCircuitExponent_def]
  have h := rectangularNaiveUpper ℚ 1 zero_le_one
  rw [show (2 : ℝ) + 1 = 3 by norm_num] at h
  exact h

end CSLibExtTest.Complexity.Algebraic.DualMatrixMultiplicationBoundsRectangularNaiveUpper
