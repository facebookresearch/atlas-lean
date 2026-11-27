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
# Tensor–Hom adjunctions for additive monoids and groups

For additive commutative monoids M,N,P, biadditive maps M×N→P correspond additively to maps
M⊗_ℕN→P. For additive commutative groups the same adjunction uses M⊗_ℤN. In both cases the
lifted map sends m⊗n to the biadditive value at (m,n).

Source attribution: upstream PR #42860, head 4d9c97ac1bb4deb8ce8e6005aca99087372c2d77,
Mathlib/LinearAlgebra/TensorProduct/Basic.lean, blob 61735e82d976a6d4f826ec81222eb056720b80a1.
-/

@[expose] public section

namespace TensorProduct

/-- **Additive maps on a tensor product are determined by pure tensors.**

Let R be a commutative semiring, M,N additive commutative R-modules and P an additive
commutative monoid. If additive maps g,h:M⊗_RN→P satisfy g(m⊗n)=h(m⊗n) for every m,n, then
g=h. Source attribution: upstream PR #42860.
-/
private theorem extAdd {R : Type*} [CommSemiring R] {M N P₂ : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P₂] [Module R M] [Module R N]
    {F : Type*} [FunLike F (M ⊗[R] N) P₂] [AddMonoidHomClass F (M ⊗[R] N) P₂]
    {g h : F} (H : ∀ (x : M) (y : N), g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h := by
  apply DFunLike.ext _ _ fun t ↦ t.inductionOn H fun x y ha hb ↦ by
    simp only [map_add, ha, hb]

/-- **Additive tensor–Hom adjunction over the natural numbers.**

Let M,N,P be additive commutative monoids. The additive equivalence liftAddEquivNat:(M→+
(N→+P))≃+(M⊗_ℕN→+P) sends a biadditive F to its unique tensor lift, with lift(F)(m⊗n)=F(m)(n).
-/
def liftAddEquivNat {M N P : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [AddCommMonoid P] : (M →+ N →+ P) ≃+ (M ⊗[ℕ] N →+ P) := .symm
  { toFun := (LinearMap.toAddMonoidHom'.comp (TensorProduct.mk ℕ M N).toAddMonoidHom).compr₂
    invFun f := liftAddHom f fun _ _ _ ↦ by simp
    map_add' _ _ := rfl
    left_inv f := by
      apply extAdd
      intro _ _
      rfl }

/-- **Additive tensor–Hom adjunction over the integers.**

Let M,N,P be additive commutative groups. The additive equivalence liftAddEquivInt:(M→+
(N→+P))≃+(M⊗_ℤN→+P) sends F to the tensor lift with value lift(F)(m⊗n)=F(m)(n).
-/
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
