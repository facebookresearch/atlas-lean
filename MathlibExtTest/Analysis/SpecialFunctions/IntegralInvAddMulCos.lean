/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.IntegralInvAddMulCos
import Mathlib.Tactic.NormNum.RealSqrt

/-! # Tests for the reciprocal cosine integral -/

open MathlibExt.Analysis.SpecialFunctions.IntegralInvAddMulCosWanted Real

-- A zero cosine coefficient gives a constant integrand for every positive a.
example (a : ℝ) (ha : 0 < a) : (∫ _ in 0..2 * π, 1 / a) = 2 * π / a := by
  simpa [Real.sqrt_sq ha.le] using integral_one_div_add_mul_cos_eq a 0 (by simpa using ha)

-- A negative coefficient gives a nonconstant example with an exact square root.
example : (∫ θ in 0..2 * π, 1 / (5 - 3 * cos θ)) = π / 2 := by
  have h := integral_one_div_add_mul_cos_eq 5 (-3) (by norm_num)
  norm_num [sub_eq_add_neg, neg_mul] at h ⊢
  linarith
