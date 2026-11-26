/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.FiniteSumsFibLucasAddFibBetaPowEqSumGenLucasCoeff
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.NumberTheory.FiniteSumsFibLucasAddFibBetaPowEqSumGenLucasCoeff

open MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

-- At exponent zero, the theorem determines the first Genocchi–Lucas coefficient.
example : genLucasCoeff 0 = 2 * Real.sqrt 5 := by
  have h5 : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 5)
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h := add_fibBeta_pow_eq_sum_genLucasCoeff 0 0
  simp at h
  have e : (2 : ℝ) * Real.sqrt 5 * ((Real.sqrt 5)⁻¹ * 2⁻¹ * genLucasCoeff 0)
      = genLucasCoeff 0 := by field_simp
  calc genLucasCoeff 0
      = 2 * Real.sqrt 5 * ((Real.sqrt 5)⁻¹ * 2⁻¹ * genLucasCoeff 0) := e.symm
    _ = 2 * Real.sqrt 5 * 1 := by rw [← h]
    _ = 2 * Real.sqrt 5 := by ring

-- At `m = 1` and `x = 0`, the theorem determines the second coefficient.
example : genLucasCoeff 1 = 2 * Real.sqrt 5 * fibBeta := by
  have h5 : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 5)
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h := add_fibBeta_pow_eq_sum_genLucasCoeff 1 0
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h
  simp at h
  have e : (2 : ℝ) * Real.sqrt 5 * ((Real.sqrt 5)⁻¹ * 2⁻¹ * genLucasCoeff 1)
      = genLucasCoeff 1 := by field_simp
  calc genLucasCoeff 1
      = 2 * Real.sqrt 5 * ((Real.sqrt 5)⁻¹ * 2⁻¹ * genLucasCoeff 1) := e.symm
    _ = 2 * Real.sqrt 5 * fibBeta := by rw [← h]

end MathlibExtTest.NumberTheory.FiniteSumsFibLucasAddFibBetaPowEqSumGenLucasCoeff
