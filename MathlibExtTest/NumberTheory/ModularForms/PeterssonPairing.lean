/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.PeterssonPairing

@[expose] public section

open scoped UpperHalfPlane

/-- The `exactSource` consumer: the pairing identity with the original
binders (nonzero level `N`, arbitrary integer weight `k`). -/
private theorem petersson_add_left_exactSource {N : ℕ} {k : ℤ} [NeZero N]
    (f₁ f₂ g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (f₁ + f₂) g = CuspForm.petersson f₁ g + CuspForm.petersson f₂ g :=
  CuspForm.petersson_add_left f₁ f₂ g

example {N : ℕ} {k : ℤ} [NeZero N] (g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (0 + 0) g = CuspForm.petersson 0 g + CuspForm.petersson 0 g := by
  exact CuspForm.petersson_add_left 0 0 g

example {N : ℕ} {k : ℤ} [NeZero N] (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (f + 0) g = CuspForm.petersson f g + CuspForm.petersson 0 g := by
  exact CuspForm.petersson_add_left f 0 g
