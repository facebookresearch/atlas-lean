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
# Naturality of the `ℤ`/`ZMod n` tensor comparison

The canonical equivalence from tensoring two `ZMod n` modules over `ℤ`
to tensoring them over `ZMod n` is natural in a pair of `ZMod n`-linear
maps.  The statement is made over `ℤ` after forgetting the scalar
structure on the target tensor product.

The result includes `n = 0`.
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

/-- Naturality of `zmodRestrictIntEquiv` under a pair of `ZMod n`-linear
maps. -/
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
