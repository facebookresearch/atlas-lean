/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.DiscriminantImPowSixInvariant

@[expose] public section

namespace MetaMathlibExt

open UpperHalfPlane ModularForm

/-- Under `S : τ ↦ -1 / τ`, `η²⁴` picks up the factor `τ¹²`. -/
example (τ : ℍ) :
    eta (((0 : ℤ) * (τ : ℂ) + (-1 : ℤ)) / ((1 : ℤ) * τ + (0 : ℤ))) ^ 24 =
      ((1 : ℤ) * (τ : ℂ) + (0 : ℤ)) ^ 12 * eta τ ^ 24 :=
  (discriminant_im_pow_six_invariant τ 0 (-1) 1 0 (by norm_num)).2.2.2.1

/-- Under `T : τ ↦ τ + 1`, `|η(τ)²⁴| (Im τ)⁶` is unchanged. -/
example (τ : ℍ) :
    ‖eta (((1 : ℤ) * (τ : ℂ) + (1 : ℤ)) / ((0 : ℤ) * τ + (1 : ℤ))) ^ 24‖ *
        ((((1 : ℤ) * (τ : ℂ) + (1 : ℤ)) / ((0 : ℤ) * τ + (1 : ℤ))).im) ^ 6 =
      ‖eta τ ^ 24‖ * (τ : ℂ).im ^ 6 :=
  (discriminant_im_pow_six_invariant τ 1 1 0 1 (by norm_num)).2.2.2.2

end MetaMathlibExt
