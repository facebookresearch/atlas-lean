/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.DigitSumPartialSum
import Mathlib.Tactic.NormNum

open Real

namespace MetaMathlibExt

-- At the initial endpoint the inclusive sum contains the digit of 1.
example : (((2 : ℕ) : ℝ) - 1) / (2 * log (↑(2 : ℕ))) * 1 * log 1 +
    1 * trollopeDelangeFluctuation 2 (log 1 / log (↑(2 : ℕ))) - trollopeDelangeSeries 2 1 +
      (1 + ⌊(1 : ℝ)⌋₊ - 1) * ((Nat.digits 2 ⌊(1 : ℝ)⌋₊).sum : ℝ) = 1 := by
  rw [← digitSum_partialSum_trollopeDelange 2 (by decide) 1 le_rfl, Nat.floor_one]
  simp

-- The inclusive ternary sum at 11/2 is 9, with a nonzero final-interval correction.
example : (((3 : ℕ) : ℝ) - 1) / (2 * log (↑(3 : ℕ))) * (11 / 2) * log (11 / 2) +
    (11 / 2) * trollopeDelangeFluctuation 3 (log (11 / 2) / log (↑(3 : ℕ))) -
      trollopeDelangeSeries 3 (11 / 2) +
      (1 + ⌊(11 / 2 : ℝ)⌋₊ - 11 / 2) * ((Nat.digits 3 ⌊(11 / 2 : ℝ)⌋₊).sum : ℝ) = 9 := by
  rw [← digitSum_partialSum_trollopeDelange 3 (by decide) (11 / 2) (by norm_num),
    show ⌊(11 / 2 : ℝ)⌋₊ = 5 by
      exact (Nat.floor_eq_iff (by norm_num)).mpr ⟨by norm_num, by norm_num⟩]
  exact_mod_cast (show (∑ i ∈ Finset.Icc 1 5, (Nat.digits 3 i).sum) = 9 by decide)

end MetaMathlibExt
