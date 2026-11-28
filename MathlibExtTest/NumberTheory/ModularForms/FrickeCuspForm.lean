/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.FrickeCuspForm

open ModularForm CongruenceSubgroup UpperHalfPlane

open scoped ModularForm MatrixGroups

#check @ModularForm.frickeGL_mul_mapGL_mul_inv
#check @ModularForm.toConjAct_frickeGL_inv_smul
#check @UpperHalfPlane.coe_frickeGL_smul
#check @CuspForm.fricke
#check @CuspForm.coe_fricke
#check @CuspForm.fricke_apply_two
#check @CuspForm.fricke_fricke_two
#check @ModularForm.fricke_involution_weight_two

-- `W₁` fixes the point `i` of the upper half-plane: `-1/(1 · i) = i`.
example : ((frickeGL 1 • UpperHalfPlane.I : ℍ) : ℂ) = Complex.I := by
  rw [coe_frickeGL_smul]
  simp

-- `W₁₁²` acts trivially on `S₂(Γ₀(11))`.
example (f : CuspForm (Gamma0 11) 2) : CuspForm.fricke 11 2 (CuspForm.fricke 11 2 f) = f :=
  CuspForm.fricke_fricke_two 11 f

-- The Fricke operator on cusp forms is `ℂ`-linear, in any weight.
example (f g : CuspForm (Gamma0 37) 4) (c : ℂ) :
    CuspForm.fricke 37 4 (c • f + g) = c • CuspForm.fricke 37 4 f + CuspForm.fricke 37 4 g := by
  simp

-- The Fricke involution of a weight-two cusp form for `Γ₀(37)` at `z`.
example (f : CuspForm (Gamma0 37) 2) (z : ℍ) :
    CuspForm.fricke 37 2 f z = (37 : ℂ)⁻¹ * (z : ℂ) ^ (-2 : ℤ) * f (frickeGL 37 • z) := by
  simpa using CuspForm.fricke_apply_two 37 f z
