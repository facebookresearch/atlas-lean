/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.CatalanDigammaSeries
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The Catalan digamma series at the half-integer parameter -/

namespace MetaMathlibExt.CatalanDigammaSeriesTest

example :
    ∑' n : ℕ, (catalan n : ℂ) / (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (1 / 2 + j : ℂ) / j) =
      2 * Complex.log 2 := by
  have h := tsum_catalan_div_four_pow_mul_binom (z := 1 / 2) (by norm_num)
  rw [show (1 / 2 + 1 / 2 : ℂ) = 1 by norm_num, Complex.digamma_one_half, Complex.digamma_one] at h
  rw [h]
  ring

end MetaMathlibExt.CatalanDigammaSeriesTest
