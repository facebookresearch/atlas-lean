/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasPeriodAverageLucasUSumDvdIffOfPEqOne
import Mathlib.Algebra.BigOperators.Intervals

/-! # Tests for divisibility of Lucas sums when `P = 1` -/

namespace MathlibExtTest.NumberTheory.Recurrences.LucasPeriodAverageLucasUSumDvdIffOfPEqOne

-- At `n = 2` the Fibonacci sum `1 + 1` is even, as `U_4 = 3 ≡ 1` modulo `2`.
example : (2 : ℤ) ∣ ∑ i ∈ Finset.Icc 1 2,
    MetaMathlibExt.lucasU MetaMathlibExt.fibonacciLucasParams i := by
  have hiff := MetaMathlibExt.lucasU_sum_dvd_iff_of_p_eq_one
    MetaMathlibExt.fibonacciLucasParams rfl 2 (by decide)
    isCoprime_one_right.neg_right
  exact hiff.mpr (by decide)

-- At `n = 4` the Fibonacci sum is `7`, not divisible by `4`, as `U_6 = 8 ≢ 1` modulo `4`.
example : ¬ (4 : ℤ) ∣ ∑ i ∈ Finset.Icc 1 4,
    MetaMathlibExt.lucasU MetaMathlibExt.fibonacciLucasParams i := by
  have hiff := MetaMathlibExt.lucasU_sum_dvd_iff_of_p_eq_one
    MetaMathlibExt.fibonacciLucasParams rfl 4 (by decide)
    isCoprime_one_right.neg_right
  have hmod : ¬ MetaMathlibExt.lucasU MetaMathlibExt.fibonacciLucasParams (4 + 2) ≡
      1 [ZMOD 4] := by decide
  exact mt hiff.mp hmod

end MathlibExtTest.NumberTheory.Recurrences.LucasPeriodAverageLucasUSumDvdIffOfPEqOne
