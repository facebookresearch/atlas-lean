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
# Additive tensor–Hom equivalences

For commutative additive monoids, a map additive separately in two variables is equivalent to an
additive map from their tensor product over ℕ. For commutative additive groups, the analogous
equivalence uses the tensor product over ℤ. In both cases the forward map evaluates on a pure
tensor x⊗y as the original two-variable map at (x,y), and pure-tensor extensionality determines
the resulting map uniquely.
-/

@[expose] public section

namespace TensorProduct

/-- Let R be a commutative semiring, M and N commutative additive monoids with R-module structures,
and P a commutative additive monoid. If g,h : M ⊗_R N → P are additive maps, in any common
function type carrying an additive-map structure, and g(x⊗y) = h(x⊗y) for all x ∈ M and y ∈ N,
then g = h. No R-module structure on P is required. -/
private theorem extAdd {R : Type*} [CommSemiring R] {M N P₂ : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P₂] [Module R M] [Module R N]
    {F : Type*} [FunLike F (M ⊗[R] N) P₂] [AddMonoidHomClass F (M ⊗[R] N) P₂]
    {g h : F} (H : ∀ (x : M) (y : N), g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h := by
  apply DFunLike.ext _ _ fun t ↦ t.inductionOn H fun x y ha hb ↦ by
    simp only [map_add, ha, hb]

/-- For commutative additive monoids M,N,P, there is an additive equivalence between maps M →
Hom_add(N,P) additive in the first variable and additive maps M ⊗_ℕ N → P. The forward map sends
a separately additive f to the unique additive map with value f(x)(y) on x⊗y; the inverse sends
g to (x,y) ↦ g(x⊗y). -/
def liftAddEquivNat {M N P : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [AddCommMonoid P] : (M →+ N →+ P) ≃+ (M ⊗[ℕ] N →+ P) := .symm
  { toFun := (LinearMap.toAddMonoidHom'.comp (TensorProduct.mk ℕ M N).toAddMonoidHom).compr₂
    invFun f := liftAddHom f fun _ _ _ ↦ by simp
    map_add' _ _ := rfl
    left_inv f := by
      apply extAdd
      intro _ _
      rfl }

/-- For commutative additive groups M,N,P, there is an additive equivalence (M → Hom_add(N,P)) ≅
Hom_add(M ⊗_ℤ N,P), with the left-hand maps additive in M. It sends f to the additive map x⊗y ↦
f(x)(y), and its inverse sends g to (x,y) ↦ g(x⊗y). -/
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
