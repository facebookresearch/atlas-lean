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

Let M,N,M′,N′ be ZMod(n)-modules in independent carrier universes, with n∈ℕ. For residue-linear
maps f:M→M′ and g:N→N′, the canonical equivalence from integer tensoring to residue tensoring
commutes with f⊗g.

The equation is ℤ-linear after restricting the residue tensor maps to their additive integer
actions. It holds for n=0 as well as positive moduli.
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

/-- For n∈ℕ and ZMod(n)-linear f:M→M′, g:N→N′ in independent carrier universes, let
e_{M,N}:M⊗_ℤN≅M⊗_{ZMod(n)}N be the canonical comparison. Then
(f⊗_{ZMod(n)}g)|_ℤ∘e_{M,N}=e_{M′,N′}∘(f|_ℤ⊗_ℤg|_ℤ). This is equality of ℤ-linear maps and
includes n=0. -/
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
