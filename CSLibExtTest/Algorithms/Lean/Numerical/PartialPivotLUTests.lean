/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Numerical.PartialPivotLU
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Regression examples for partial-pivot LU -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Numerical.PartialPivotLU.Tests

open Matrix

-- The pivot is selected by magnitude, not by signed value or row order.
private def swapNeeded : Matrix (Fin 2) (Fin 2) ℚ := !![1, 3; -2, 4]

example : (factor swapNeeded).perm 0 = 1 ∧
    (factor swapNeeded).lower 1 0 = -1 / 2 ∧ (factor swapNeeded).upper 1 1 = 5 := by
  decide +kernel

-- Tied pivots keep the first row. The last column attains the factor-of-two growth bound.
private def tight : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; -1, 1]

example : (factor tight).perm 0 = 0 ∧
    (factor tight).lower 1 0 = -1 ∧ (factor tight).upper 1 1 = 2 := by
  decide +kernel

-- A zero pivot column leaves the remaining column unchanged, even for a singular input.
private def zeroColumn : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 2]

example : (factor zeroColumn).lower 1 0 = 0 ∧ (factor zeroColumn).upper 1 1 = 2 := by
  decide +kernel

-- The second pivot swaps the lower rows. Their first-column multipliers must move with them.
private def laterSwap : Matrix (Fin 3) (Fin 3) ℚ := !![4, 0, 2; 2, 1, -1; 1, 3, 2]

example : (factor laterSwap).perm 1 = 2 ∧ (factor laterSwap).perm 2 = 1 ∧
    (factor laterSwap).lower 1 0 = 1 / 4 ∧ (factor laterSwap).lower 2 0 = 1 / 2 ∧
    (factor laterSwap).upper 2 2 = -5 / 2 := by
  decide +kernel

-- Two consecutive eliminations can double the last column twice.
private def twiceTight : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; -1, 1, 1; -1, -1, 1]

example : (factor twiceTight).upper 2 2 = 4 := by
  decide +kernel

-- Two overlapping swaps produce a three-cycle, not its inverse.
private def cycleNeeded : Matrix (Fin 3) (Fin 3) ℚ := !![2, 1, -1; 4, 0, 2; 1, 3, 2]

example : (factor cycleNeeded).perm 0 = 1 ∧ (factor cycleNeeded).perm 1 = 2 ∧
    (factor cycleNeeded).perm 2 = 0 := by
  decide +kernel

end Cslib.Algorithms.Lean.Numerical.PartialPivotLU.Tests
