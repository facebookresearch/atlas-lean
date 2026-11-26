/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Canonical scalar restriction with the original compatible module action. -/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Algebra.Tower

/-!
# Compatible ground actions and scalar restriction

For a commutative ring `k`, a ring algebra `R` over `k`, and a module `M` with compatible `k`-
and `R`-actions, restriction along `algebraMap k R` has a `k`-linear identity comparison with
the given ground action on `M`.

The comparison and its inverse preserve every element of the carrier, and they commute with
acting-ring-linear maps.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v w

namespace ModuleCat

variable (k : Type u) [CommRing k] (R : Type v) [Ring R] [Algebra k R]
  (M : Type w) [AddCommGroup M] [mk : Module k M] [mr : Module R M] [tower : IsScalarTower k R M]

/-- Let `k` be a commutative ring, `R` a `k`-algebra with possibly noncommutative underlying ring,
and `M` have `k`- and `R`-module structures satisfying `IsScalarTower k R M`. The
scalar-restricted object `restrictScalars(algebraMap k R)(M_R)` is `k`-linearly equivalent to
the given module `M_k` by the identity on elements, with identity inverse. -/
def compatibleRestrictScalarsEquiv :
    ((ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R M)) ≃ₗ[k] M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c m := by
    erw [ModuleCat.restrictScalars.smul_def]
    exact @IsScalarTower.algebraMap_smul k R M _ _ _ mr.toMulAction mk.toSMul tower c (m : M)

/-- Let `k` be a commutative ring, `R` a `k`-algebra with possibly noncommutative underlying ring,
and `M` have `k`- and `R`-module structures satisfying `IsScalarTower k R M`. For an element
`m` of the scalar-restricted module, `compatibleRestrictScalarsEquiv k R M m=m`. -/
@[simp]
theorem compatibleRestrictScalarsEquiv_apply
    (m : (ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R M)) :
    compatibleRestrictScalarsEquiv k R M m = m := rfl

/-- Let `k` be a commutative ring, `R` a `k`-algebra with possibly noncommutative underlying ring,
and `M` have `k`- and `R`-module structures satisfying `IsScalarTower k R M`. For `m : M`,
`(compatibleRestrictScalarsEquiv k R M).symm m=m`. -/
@[simp]
theorem compatibleRestrictScalarsEquiv_symm_apply (m : M) :
    (compatibleRestrictScalarsEquiv k R M).symm m = m := rfl

/-- Let `k` be a commutative ring, `R` a `k`-algebra with possibly noncommutative underlying ring,
and `M` have `k`- and `R`-module structures satisfying `IsScalarTower k R M`. Let `N` have the
same compatible structures and `f : M →ₗ[R] N`. With identity comparisons `E_M,E_N`, `E_N ∘
restrictScalars(f)=f.restrictScalars k ∘ E_M` as maps of `k`-modules. -/
theorem compatibleRestrictScalarsEquiv_naturality
    {N : Type w} [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
    (f : M →ₗ[R] N) :
    (compatibleRestrictScalarsEquiv k R N).toLinearMap.comp
        (((ModuleCat.restrictScalars (algebraMap k R)).map (ModuleCat.ofHom f)).hom) =
      (f.restrictScalars k).comp (compatibleRestrictScalarsEquiv k R M).toLinearMap := by
  ext m
  rfl

end ModuleCat
