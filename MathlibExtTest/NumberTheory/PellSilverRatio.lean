/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellSilverRatio

open MetaMathlibExt

-- At the initial even index the excess is √2, which is greater than one.
example : 1 < (pellLucasSequence 0 : ℝ) * (1 + Real.sqrt 2) - pellLucasSequence 1 := by
  have h := sub_eq_iff_eq_add'.mpr (pellNumber_odd_mul_one_add_sqrt_two 0).2
  simp only [Nat.mul_zero, Nat.zero_add, pow_zero, mul_one] at h
  rw [h, Real.lt_sqrt zero_le_one]
  norm_num

-- The first noninitial pair uses P₃ = 5, P₄ = 12 and H₂ = 3, H₃ = 7.
example : (5 : ℝ) * (1 + Real.sqrt 2) = 12 + (Real.sqrt 2 - 1) ^ 3 ∧
    (3 : ℝ) * (1 + Real.sqrt 2) = 7 + Real.sqrt 2 * (Real.sqrt 2 - 1) ^ 2 := by
  exact pellNumber_odd_mul_one_add_sqrt_two 1
