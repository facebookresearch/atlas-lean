/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import MathlibExt.Analysis.SpecialFunctions.Gamma.BetaPowerProduct

-- The constant-integrand endpoint and a nonconstant case.
example : (∫ x in (0 : ℝ)..1, x ^ (0 : ℕ) * (1 - x) ^ (0 : ℕ)) = 1 := by
  norm_num [intervalIntegral.integral_pow_one_sub_pow]

example : (∫ x in (0 : ℝ)..1, x ^ (1 : ℕ) * (1 - x) ^ (1 : ℕ)) = 1 / 6 := by
  rw [intervalIntegral.integral_pow_one_sub_pow]
  norm_num [Nat.choose]
