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
# Scalar restriction agrees with an original compatible ground action

The native restriction functor uses Module.compHom along algebraMap. An
original ground module with the actual scalar tower has the same values.
The comparison is the identity on the original carrier; no Small or chosen
comparison premise is required. Ground, algebra and carrier sizes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v w

namespace ModuleCat

variable (k : Type u) [CommRing k] (R : Type v) [Ring R] [Algebra k R]
  (M : Type w) [AddCommGroup M] [mk : Module k M] [mr : Module R M] [tower : IsScalarTower k R M]

/-- Native restriction has an actual ground-linear identity comparison to the original compatible action. -/
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

/-- The forward comparison is the identity on the original coefficient carrier. -/
@[simp]
theorem compatibleRestrictScalarsEquiv_apply
    (m : (ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R M)) :
    compatibleRestrictScalarsEquiv k R M m = m := rfl

/-- The inverse comparison also retains the original coefficient carrier. -/
@[simp]
theorem compatibleRestrictScalarsEquiv_symm_apply (m : M) :
    (compatibleRestrictScalarsEquiv k R M).symm m = m := rfl

/-- Scalar-restriction comparison is natural in original acting-ring-linear maps. -/
theorem compatibleRestrictScalarsEquiv_naturality
    {N : Type w} [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
    (f : M →ₗ[R] N) :
    (compatibleRestrictScalarsEquiv k R N).toLinearMap.comp
        (((ModuleCat.restrictScalars (algebraMap k R)).map (ModuleCat.ofHom f)).hom) =
      (f.restrictScalars k).comp (compatibleRestrictScalarsEquiv k R M).toLinearMap := by
  ext m
  rfl

end ModuleCat
