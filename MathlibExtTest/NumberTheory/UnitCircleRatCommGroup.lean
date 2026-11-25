/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.UnitCircleRatCommGroup

/-! # Tests for Amato's group law on rational unit-circle points -/

open MetaMathlibExt

-- Closure includes products of points with opposite signs in their first coordinates.
example :
    unitCircleRatMul (-3 / 5, 4 / 5) (3 / 5, 4 / 5) ∈
      {p : ℚ × ℚ | p.1 ≠ 0 ∧ p.1 ^ 2 + p.2 ^ 2 = 1} := by
  apply unitCircleRat_commGroup.2.1 <;> norm_num

-- The inverse preserves the sign of the first coordinate.
example : unitCircleRatMul (-3 / 5, 4 / 5) (-3 / 5, -4 / 5) = (1, 0) := by
  have hp : ((-3 / 5, 4 / 5) : ℚ × ℚ) ∈
      {p : ℚ × ℚ | p.1 ≠ 0 ∧ p.1 ^ 2 + p.2 ^ 2 = 1} := by
    norm_num
  simpa only [neg_div] using unitCircleRat_commGroup.2.2.2.2.2.1 _ hp
