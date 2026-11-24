/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

-- BACKPORT: Extracted from PR #42860 head `4d9c97ac1bb4deb8ce8e6005aca99087372c2d77`,
-- path `Mathlib/LinearAlgebra/TensorProduct/Basic.lean`,
-- blob `61735e82d976a6d4f826ec81222eb056720b80a1`, authors Junyan Xu.
-- See `BACKPORTS.md` for copied surface, adaptations, and upgrade-removal steps.

public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor–Hom equivalences for additive maps

Additive bilinear maps over the natural numbers and integers correspond to additive maps from the
tensor product. Pure-tensor extensionality characterizes the maps and their inverses.
-/

@[expose] public section

namespace TensorProduct

/-- Additive maps on a tensor product are equal when they agree on pure tensors. -/
private theorem extAdd {R : Type*} [CommSemiring R] {M N P₂ : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P₂] [Module R M] [Module R N]
    {F : Type*} [FunLike F (M ⊗[R] N) P₂] [AddMonoidHomClass F (M ⊗[R] N) P₂]
    {g h : F} (H : ∀ (x : M) (y : N), g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h := by
  apply DFunLike.ext _ _ fun t ↦ t.inductionOn H fun x y ha hb ↦ by
    simp only [map_add, ha, hb]

/-- The adjunction between tensor product over ℕ and internal hom in the category of
`AddCommMonoid`s. -/
def liftAddEquivNat {M N P : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [AddCommMonoid P] : (M →+ N →+ P) ≃+ (M ⊗[ℕ] N →+ P) := .symm
  { toFun := (LinearMap.toAddMonoidHom'.comp (TensorProduct.mk ℕ M N).toAddMonoidHom).compr₂
    invFun f := liftAddHom f fun _ _ _ ↦ by simp
    map_add' _ _ := rfl
    left_inv f := by
      apply extAdd
      intro _ _
      rfl }

/-- The adjunction between tensor product over ℤ and internal hom in the category of
`AddCommGroup`s. -/
def liftAddEquivInt {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] :
    (M →+ N →+ P) ≃+ (M ⊗[ℤ] N →+ P) := .symm
  { toFun := (LinearMap.toAddMonoidHom'.comp (TensorProduct.mk ℤ M N).toAddMonoidHom).compr₂
    invFun f := liftAddHom f fun _ _ _ ↦ by simp
    map_add' _ _ := rfl
    left_inv f := by
      apply extAdd
      intro _ _
      rfl }

end TensorProduct

end
