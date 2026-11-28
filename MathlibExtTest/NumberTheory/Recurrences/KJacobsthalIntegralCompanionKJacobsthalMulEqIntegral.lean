/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.KJacobsthalIntegralCompanionKJacobsthalMulEqIntegral
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Tests for the integral representation of the companion k-Jacobsthal numbers

Concrete instances of `companionKJacobsthal_mul_eq_integral`: the `n = 0` case, where the
reciprocal has a removable singularity, and positive-`n` cases with polynomial integrands.
-/

namespace MathlibExtTest.NumberTheory.Recurrences.KJacobsthalIntegralCompanionKJacobsthalMulEqIntegral

open MetaMathlibExt

-- With k = ℓ = 1 and n = 0, the reciprocal has a removable singularity at -1/3.
example : (∫ x in (-1 : ℝ)..1, (2 + 6 * x) * (1 + 3 * x)⁻¹) = 4 := by
  have h := companionKJacobsthal_mul_eq_integral 1 1 0 2 5
  norm_num [companionKJacobsthal, lucasU, lucasV, kJacobsthalParams] at h
  linarith

-- For k = 1, ℓ = 2 and n = 1 the endpoints recover 𝒥_{1,2}(3, 7) = 13.
example : (∫ x in (-1 : ℝ)..1, 26 + 18 * x) = 52 := by
  have h := companionKJacobsthal_mul_eq_integral 1 2 1 3 7
  norm_num only [companionKJacobsthal, lucasU, lucasV, kJacobsthalParams, zpow_zero,
    mul_one] at h
  linarith

-- For k = ℓ = 1 and n = 2 the endpoints recover 𝒥_{1,2}(1, 1) = 3.
example : (∫ x in (-1 : ℝ)..1, (3 + 9 * x) * (1 + 3 * x)) = 24 := by
  have h := companionKJacobsthal_mul_eq_integral 1 1 2 1 1
  norm_num [companionKJacobsthal, lucasU, lucasV, kJacobsthalParams] at h
  linarith

end MathlibExtTest.NumberTheory.Recurrences.KJacobsthalIntegralCompanionKJacobsthalMulEqIntegral
