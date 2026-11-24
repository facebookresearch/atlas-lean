/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RamanujanBinomialSine
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

-- The series still converges at the left endpoint for a nonintegral exponent.
example : HasSum
    (fun ν : ℕ => Ring.choose (1 / 2 : ℝ) ν * Real.sin ((1 + 2 * (ν : ℝ)) * (-Real.pi / 2)))
    0 := by
  have hθ : |(-Real.pi / 2)| ≤ Real.pi / 2 := by
    rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]
  simpa [neg_div, Real.cos_neg, Real.cos_pi_div_two,
    Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using
    hasSum_ringChoose_mul_sin 1 (1 / 2) (-Real.pi / 2) (by norm_num) hθ

-- At the right endpoint and N = 0, the series has sum 1, with the convention 0^0 = 1.
example : HasSum
    (fun ν : ℕ => Ring.choose (0 : ℝ) ν * Real.sin ((1 + 2 * (ν : ℝ)) * (Real.pi / 2)))
    1 := by
  have hθ : |Real.pi / 2| ≤ Real.pi / 2 := by rw [abs_of_nonneg (by positivity)]
  simpa [Real.rpow_zero, Real.sin_pi_div_two] using
    hasSum_ringChoose_mul_sin 1 0 (Real.pi / 2) le_rfl hθ
