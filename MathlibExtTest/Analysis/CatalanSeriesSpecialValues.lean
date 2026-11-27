/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.CatalanSeriesSpecialValues
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Tail regressions for the Catalan series special values -/

namespace MetaMathlibExt.CatalanSeriesSpecialValuesTest

-- The zero-index term contributes one half. Removing it gives a sum starting at one.
example :
    HasSum (fun n : ℕ ↦ (catalan (n + 1) : ℝ) / (4 ^ (n + 1) * (n + 2) * (n + 3)))
      (17 / 6 - 4 * Real.log 2) := by
  let f (n : ℕ) := (catalan n : ℝ) / (4 ^ n * (n + 1) * (n + 2))
  have h : ∑' n, f n = 10 / 3 - 4 * Real.log 2 := tsum_catalan_div_four_pow_special.2
  have hs : Summable f := by
    by_contra hn
    rw [tsum_eq_zero_of_not_summable hn] at h
    linarith [Real.log_two_lt_d9]
  have htail := (hasSum_nat_add_iff' 1).2 (hs.hasSum_iff.2 h)
  convert htail using 1
  · ext n
    simp only [f, Nat.cast_add, Nat.cast_one]
    ring
  · norm_num [f, catalan_zero]
    ring

-- The zero-index term of the first odd-weighted series contributes one.
example :
    HasSum (fun n : ℕ ↦ (2 * ((n : ℝ) + 1) + 1) / ((n : ℝ) + 2) * catalan (n + 1) /
      4 ^ (n + 1)) (4 * Real.log 2 - 1) := by
  let f (n : ℕ) : ℝ := (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * catalan n / 4 ^ n
  have h : ∑' n, f n = 4 * Real.log 2 := tsum_odd_mul_catalan_div_four_pow_special.1
  have hs : Summable f := by
    by_contra hn
    rw [tsum_eq_zero_of_not_summable hn] at h
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have htail := (hasSum_nat_add_iff' 1).2 (hs.hasSum_iff.2 h)
  convert htail using 1
  · ext n
    simp only [f, Nat.cast_add, Nat.cast_one]
    ring
  · norm_num [f, catalan_zero]

end MetaMathlibExt.CatalanSeriesSpecialValuesTest
