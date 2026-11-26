/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.TensorProduct.ZModRestrict
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Naturality of integer and residue tensor comparison

Let n∈ℕ and M,N be ZMod n-modules, regarded as integer modules on their additive groups. For
n=0, ZMod 0=ℤ. Let Θ:M⊗_ℤN≃ₗ[ℤ]M⊗_(ZMod n)N be the comparison preserving pure tensors. For
ZMod n-linear f:M→M′ and g:N→N′, the pure-preserving comparison commutes with f⊗g in both
scalar presentations, including n=0.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace TensorProduct

universe u v u' v'

variable (n : ℕ)
variable {M : Type u} {N : Type v} {M' : Type u'} {N' : Type v'}
variable [AddCommGroup M] [AddCommGroup N]
variable [AddCommGroup M'] [AddCommGroup N']
variable [Module (ZMod n) M] [Module (ZMod n) N]
variable [Module (ZMod n) M'] [Module (ZMod n) N']

/-- **Factor maps commute with the residue tensor equivalence.**

Let n∈ℕ and M,N be ZMod n-modules, regarded as integer modules on their additive groups. For
n=0, ZMod 0=ℤ. Let Θ:M⊗_ℤN≃ₗ[ℤ]M⊗_(ZMod n)N be the comparison preserving pure tensors. For
ZMod n-linear f:M→M′ and g:N→N′, (f⊗_(ZMod n)g)∘Θ_(M,N)=Θ_(M′,N′)∘(f⊗_ℤg), as integer-linear
maps.
-/
theorem zmodRestrictIntEquiv_naturality
    (f : M →ₗ[ZMod n] M') (g : N →ₗ[ZMod n] N') :
    (TensorProduct.map f g).toAddMonoidHom.toIntLinearMap.comp
        (zmodRestrictIntEquiv n M N).toLinearMap =
      (zmodRestrictIntEquiv n M' N').toLinearMap.comp
        (TensorProduct.map
          f.toAddMonoidHom.toIntLinearMap
          g.toAddMonoidHom.toIntLinearMap) := by
  apply TensorProduct.ext'
  intro x y
  rfl

end TensorProduct
