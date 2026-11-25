/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.JacobsthalOffsetIntegral
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- With n = 0 and ℓ = r = 1, the reciprocal has a removable singularity at -1/3.
example : (∫ x in (-1 : ℝ)..1, (1 + 3 * x) * (1 + 3 * x)⁻¹) = 2 := by
  have h := jacobsthal_mul_add_eq_integral 1 0 1
  norm_num [lucasU, lucasV, kJacobsthalParams] at h
  linarith

-- For ℓ = n = 2 and r = 1 the endpoints recover J₅ = 11.
example : (∫ x in (-1 : ℝ)..1, (7 + 9 * x) * (5 + 3 * x)) = 88 := by
  have h := jacobsthal_mul_add_eq_integral 2 2 1
  norm_num [lucasU, lucasV, kJacobsthalParams] at h
  linarith
