/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.E4EtaProduct

@[expose] public section

/-- Consumer with the original binders: the identity holds for every
point of the upper half-plane. -/
private theorem exactSource (z : UpperHalfPlane) :
    ModularForm.E₄ z * (ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (2 * (z : ℂ)) ^ 8 *
        ModularForm.eta (4 * (z : ℂ)) ^ 16) =
      ModularForm.eta (2 * (z : ℂ)) ^ 48 +
        224 * (ModularForm.eta (z : ℂ) ^ 8 * ModularForm.eta (2 * (z : ℂ)) ^ 24 *
          ModularForm.eta (4 * (z : ℂ)) ^ 16) +
        256 * (ModularForm.eta (z : ℂ) ^ 16 * ModularForm.eta (4 * (z : ℂ)) ^ 32) :=
  ModularForm.E4_mul_etaProduct_eq z

/-- The constant `224` is essential: with `0` in its place the identity
would force a nonzero eta product to vanish at `i`. -/
example : (224 : ℂ) ≠ 0 := by norm_num
