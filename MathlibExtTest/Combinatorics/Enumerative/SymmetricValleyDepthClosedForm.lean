/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SymmetricValleyDepthClosedForm

/-! # Special values of the symmetric valley depth closed form -/

open MetaMathlibExt

namespace MathlibExtTest.SymmetricValleyDepthClosedForm

private theorem sq_i_sqrt_three : (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2 = -3 := by
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

-- All terms cancel for the empty composition.
example : (∑ c : Composition 0, symmetricValleyDepthSum c.blocks : ℕ) = 0 := by
  apply (Nat.cast_inj (R := ℂ)).mp
  rw [symmetricValleyDepthSum_compositions_closed_form]
  rw [mul_assoc 15, mul_comm (Real.sqrt 3 : ℂ) Complex.I]
  generalize hz : Complex.I * (Real.sqrt 3 : ℂ) = z
  have h : z ^ 2 = -3 := hz ▸ sq_i_sqrt_three
  have hprod : (1 + z) * (1 - z) = 4 := by linear_combination -h
  have hn : (1 + z) * (1 - z) ≠ 0 := hprod.trans_ne (by norm_num)
  obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hn
  norm_num
  field_simp
  grind

-- The example in the paper includes overlapping valleys in the composition 21212.
example : (∑ c : Composition 8, symmetricValleyDepthSum c.blocks : ℕ) = 17 := by
  apply (Nat.cast_inj (R := ℂ)).mp
  rw [symmetricValleyDepthSum_compositions_closed_form]
  have h := sq_i_sqrt_three
  have hp : (1 + Complex.I * (Real.sqrt 3 : ℂ)) ^ 3 = -8 := by
    linear_combination (Complex.I * (Real.sqrt 3 : ℂ) + 3) * h
  have hm : (1 - Complex.I * (Real.sqrt 3 : ℂ)) ^ 3 = -8 := by
    linear_combination (3 - Complex.I * (Real.sqrt 3 : ℂ)) * h
  rw [show 8 + 1 = 3 * 3 by decide, pow_mul, pow_mul, hp, hm]
  push_cast
  ring

end MathlibExtTest.SymmetricValleyDepthClosedForm
