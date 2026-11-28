/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.EtaBound

/-!
# Tests for the explicit upper bound for `‖η(τ)‖ ^ 24 (Im τ) ^ 6`
-/

open UpperHalfPlane

#check @ModularForm.norm_tprod_one_sub_pow_le
#check @ModularForm.norm_eta_le
#check @ModularForm.norm_eta_pow_mul_im_pow_le_of_mem_fd
#check @ModularForm.norm_eta_pow_mul_im_pow_le

/-- The bound at the point `i` of the fundamental domain. -/
example : ‖ModularForm.eta (UpperHalfPlane.I : ℂ)‖ ^ 24 * UpperHalfPlane.I.im ^ 6 ≤ 1 / 64 :=
  ModularForm.norm_eta_pow_mul_im_pow_le_of_mem_fd _ ModularGroup.I_mem_fd

/-- The bound in terms of the discriminant `Δ = η ^ 24`, at an arbitrary point. -/
example (τ : ℍ) : ‖ModularForm.discriminant τ‖ * τ.im ^ 6 ≤ 1 / 64 := by
  simpa [ModularForm.discriminant, norm_pow] using ModularForm.norm_eta_pow_mul_im_pow_le τ

/-- The product bound at `q = 1 / 2`. -/
example :
    ‖∏' n : ℕ, (1 - (1 / 2 : ℂ) ^ (n + 1))‖ ≤ Real.exp (‖(1 / 2 : ℂ)‖ / (1 - ‖(1 / 2 : ℂ)‖)) :=
  ModularForm.norm_tprod_one_sub_pow_le (by norm_num)
