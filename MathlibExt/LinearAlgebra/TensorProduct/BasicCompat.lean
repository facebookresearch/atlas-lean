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
# Tensor-hom adjunctions over `ℕ` and `ℤ` (backport)

Backports `TensorProduct.liftAddEquivNat` and `TensorProduct.liftAddEquivInt`
from upstream PR #42860 (head `4d9c97ac1bb4deb8ce8e6005aca99087372c2d77`,
path `Mathlib/LinearAlgebra/TensorProduct/Basic.lean`,
blob `61735e82d976a6d4f826ec81222eb056720b80a1`).

The upstream PR additionally generalizes `TensorProduct.ext'`,
`TensorProduct.ext_threefold`, and `TensorProduct.ext_threefold'` in place from
linear maps to `AddMonoidHomClass` maps. Those generalizations cannot be carried
under their upstream names: the pinned Mathlib already declares `ext'`,
`ext_threefold`, and `ext_threefold'` with the narrower linear-map statements.
They are therefore not exposed as public API at all: each backport file that
needs the generality (this file, `Grp/Monoidal`, `Presheaf/MonoidalCompat`,
`Sheaf/MonoidalCore`) carries a file-private copy under the distinct local name
`extAdd` / `ext_threefoldAdd`; on removal those private uses are replaced by the
upstream `ext'` / `ext_threefold` with nothing to rename elsewhere.
-/

@[expose] public section

namespace TensorProduct

/-- File-private pending-upstream generality: upstream PR #42860 generalizes
`TensorProduct.ext'` from linear maps to `AddMonoidHomClass` maps. The pinned
Mathlib already declares `ext'` with the narrow linear-map statement, so this
backport file uses a file-private copy under the distinct name `extAdd`.
On removal of the backport, replace uses by upstream `TensorProduct.ext'`. -/
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
