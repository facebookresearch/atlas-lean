/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.PowerSumMatrixBinomialRatio
import Mathlib.Tactic.NormNum

namespace MathlibExt.LinearAlgebra.PowerSumMatrixWanted

open Finset

-- At k = 0 the single summand divides by zero.
example : ∑ r ∈ range 1,
    (-1 : ℚ) ^ r / (((0 - r : ℕ) : ℚ) * (2 * r + 1)) *
      ((0 - r).choose r : ℚ) * ((2 * r).choose r : ℚ)⁻¹ = 0 :=
  (sum_choose_div_choose_eq 0).trans (by norm_num)

-- At k = 1 the single summand has a nonzero denominator.
example : ∑ r ∈ range (1 / 2 + 1),
    (-1 : ℚ) ^ r / (((1 - r : ℕ) : ℚ) * (2 * r + 1)) *
      ((1 - r).choose r : ℚ) * ((2 * r).choose r : ℚ)⁻¹ = 1 := by
  exact (sum_choose_div_choose_eq 1).trans (by norm_num)

-- The last summand for k = 4 has k - 2r = 0.
example : ∑ r ∈ range 3,
    (-1 : ℚ) ^ r / (((4 - r : ℕ) : ℚ) * (2 * r + 1)) *
      ((4 - r).choose r : ℚ) * ((2 * r).choose r : ℚ)⁻¹ = 1 / 10 :=
  (sum_choose_div_choose_eq 4).trans (by norm_num)

-- For the odd case k = 5 the last summand has k - 2r = 1.
example : ∑ r ∈ range 3,
    (-1 : ℚ) ^ r / (((5 - r : ℕ) : ℚ) * (2 * r + 1)) *
      ((5 - r).choose r : ℚ) * ((2 * r).choose r : ℚ)⁻¹ = 1 / 15 :=
  (sum_choose_div_choose_eq 5).trans (by norm_num)

end MathlibExt.LinearAlgebra.PowerSumMatrixWanted
