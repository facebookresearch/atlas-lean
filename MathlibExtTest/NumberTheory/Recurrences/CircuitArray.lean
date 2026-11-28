/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.CircuitArray
meta import MathlibExt.NumberTheory.Recurrences.CircuitArray
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

/-! ### Evaluating the circuit array

The circuit array is computable, so its first entries can be evaluated. They agree with Table 1
of Evans and Hendel and with the closed form `C_{0,s} = (9 ^ s / 3 - 1) / (9 ^ s / 3)` of row
zero. -/

#guard circuitArray 0 1 = 2 / 3
#guard circuitArray 0 2 = 26 / 27
#guard circuitArray 0 3 = 242 / 243
#guard circuitArray 0 4 = 2186 / 2187
#guard circuitArray 1 2 = 13 / 12
#guard circuitArray 2 2 = 1 / 2
#guard (List.range 6).all fun k =>
  circuitArray 0 (k + 1) = ((9 : ℚ) ^ (k + 1) / 3 - 1) / ((9 : ℚ) ^ (k + 1) / 3)

/-! ### Row zero of the circuit array -/

example : circuitArray 0 3 = 242 / 243 := by
  rw [(circuitArrayX_row_zero 3 (by norm_num)).2]
  norm_num

-- The closed form agrees with the entries of `circuitArray_small`.
example : circuitArray 0 1 = 2 / 3 ∧ circuitArray 0 2 = 26 / 27 := by
  rw [(circuitArrayX_row_zero 1 le_rfl).2, (circuitArrayX_row_zero 2 (by norm_num)).2]
  norm_num

/-! ### Row zero of the one-variable circuit array -/

-- At `s = 1` the exponent `s - 2 = -1` is negative and the closed form is the boundary value
-- `(X - 3) / X` of `circuitArrayX_zero_one`.
example : circuitArrayX 0 1 = (RatFunc.X - 3) / RatFunc.X := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  rw [(circuitArrayX_row_zero 1 le_rfl).1, show ((1 : ℕ) : ℤ) - 2 = -1 by norm_num, zpow_neg_one]
  field_simp
  ring

example : circuitArrayX 0 2 = (3 * RatFunc.X - 1) / (3 * RatFunc.X) := by
  rw [(circuitArrayX_row_zero 2 (by norm_num)).1]
  norm_num

-- The same entry computed from the definition, by reducing the grid twice: the left edge of the
-- triangle in row `3` and diagonal `2` is `Y(Δ(1, 1, β), 1/3, 1/3) = (8 + β) / 9` for the
-- boundary value `β = (X - 3) / X`.
example : circuitArrayX 0 2 = (3 * RatFunc.X - 1) / (3 * RatFunc.X) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hX1 : (RatFunc.X - 1 : RatFunc ℚ) ≠ 0 := by
    simpa using RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero (1 : ℚ))
  norm_num [circuitArrayX, circuitArrayOf, circuitGrid, circuitReduce, circuitLeftEdge,
    circuitRightEdge, circuitBaseEdge, circuitTopArm, circuitRightArm, circuitLeftArm, circuitDelta,
    circuitY]
  rw [show (2 + (RatFunc.X - 3) / RatFunc.X : RatFunc ℚ) = 3 * (RatFunc.X - 1) / RatFunc.X by
    field_simp; ring]
  field_simp
  ring

example : circuitArrayX 0 3 = (27 * RatFunc.X - 1) / (27 * RatFunc.X) := by
  rw [(circuitArrayX_row_zero 3 (by norm_num)).1]
  norm_num

end MetaMathlibExt
