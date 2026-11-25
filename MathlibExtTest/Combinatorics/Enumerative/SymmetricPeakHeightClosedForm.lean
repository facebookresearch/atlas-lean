/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightClosedForm

/-! # Special values of the symmetric peak height closed form -/

open MetaMathlibExt

namespace MathlibExtTest.SymmetricPeakHeightClosedForm

private theorem sq_i_sqrt_three : (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2 = -3 := by
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private theorem one_add_i_sqrt_three_pow_three :
    (1 + Complex.I * (Real.sqrt 3 : ℂ)) ^ 3 = -8 := by
  linear_combination (Complex.I * (Real.sqrt 3 : ℂ) + 3) * sq_i_sqrt_three

private theorem one_sub_i_sqrt_three_pow_three :
    (1 - Complex.I * (Real.sqrt 3 : ℂ)) ^ 3 = -8 := by
  linear_combination (3 - Complex.I * (Real.sqrt 3 : ℂ)) * sq_i_sqrt_three

-- All terms cancel for the empty composition.
example : (∑ c : Composition 0, symmetricPeakHeightSum c.blocks : ℕ) = 0 := by
  apply (Nat.cast_inj (R := ℂ)).mp
  rw [symmetricPeakHeightSum_compositions_closed_form, mul_assoc 15]
  generalize hz : Complex.I * (Real.sqrt 3 : ℂ) = z
  have h : z ^ 2 = -3 := hz ▸ sq_i_sqrt_three
  have hprod : (1 + z) * (1 - z) = 4 := by linear_combination -h
  have hn : (1 + z) * (1 - z) ≠ 0 := hprod.trans_ne (by norm_num)
  obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hn
  norm_num
  field_simp
  grind

-- The compositions `1 3 1`, `1 2 1 1` and `1 1 2 1` of `5` contribute `2 + 1 + 1`, as in the
-- example after Corollary 3 of arXiv:2408.09166v1.
example : (∑ c : Composition 5, symmetricPeakHeightSum c.blocks : ℕ) = 4 := by
  apply (Nat.cast_inj (R := ℂ)).mp
  rw [symmetricPeakHeightSum_compositions_closed_form, show 5 + 1 = 3 * 2 by decide, pow_mul,
    pow_mul, one_add_i_sqrt_three_pow_three, one_sub_i_sqrt_three_pow_three]
  push_cast
  ring

-- The value agrees with the coefficient of `x⁸` in `x⁴ / ((1 - 2x)² (1 - x³))`,
-- which is `5 · 2⁴ + 2 · 2 = 84`.
example : (∑ c : Composition 8, symmetricPeakHeightSum c.blocks : ℕ) = 84 := by
  apply (Nat.cast_inj (R := ℂ)).mp
  rw [symmetricPeakHeightSum_compositions_closed_form, show 8 + 1 = 3 * 3 by decide, pow_mul,
    pow_mul, one_add_i_sqrt_three_pow_three, one_sub_i_sqrt_three_pow_three]
  push_cast
  ring

end MathlibExtTest.SymmetricPeakHeightClosedForm
