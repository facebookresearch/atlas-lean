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

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Restriction along an existing module scalar tower

A module with its existing base-ring action and an actual scalar tower is
canonically the restriction of its scalar-algebra module. The comparison
preserves the carrier and every element. The two ring universes and the module
universe are independent. No ring equivalence or surjectivity is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory

namespace ModuleCat

universe r s m

variable (R : Type r) (S : Type s) [CommRing R] [Ring S] [Algebra R S]

/-- An actual scalar tower identifies the original base-ring module
with restriction of the same carrier and its existing scalar-algebra action. -/
def restrictScalarsIsoOfScalarTower (M : ModuleCat.{m} R)
    [Module S M] [IsScalarTower R S M] :
    M ≅ (restrictScalars (algebraMap R S)).obj (ModuleCat.of S M) := by
  let N := (restrictScalars (algebraMap R S)).obj (ModuleCat.of S M)
  let e : M ≃ₗ[R] N :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => (IsScalarTower.algebraMap_smul S r x).symm }
  exact e.toModuleIso

/-- The tower comparison leaves every original element unchanged. -/
@[simp]
theorem restrictScalarsIsoOfScalarTower_hom_apply (M : ModuleCat.{m} R)
    [Module S M] [IsScalarTower R S M] (x : M) :
    (restrictScalarsIsoOfScalarTower R S M).hom x = x := rfl

/-- The inverse tower comparison also leaves every element unchanged. -/
@[simp]
theorem restrictScalarsIsoOfScalarTower_inv_apply (M : ModuleCat.{m} R)
    [Module S M] [IsScalarTower R S M]
    (x : (restrictScalars (algebraMap R S)).obj (ModuleCat.of S M)) :
    (restrictScalarsIsoOfScalarTower R S M).inv x = x := rfl

/-- Existing scalar-algebra linear maps commute with the literal tower
comparison and their canonical restriction to the original base-ring actions. -/
theorem restrictScalarsIsoOfScalarTower_hom_naturality
    {M N : ModuleCat.{m} R}
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (f : ModuleCat.of S M ⟶ ModuleCat.of S N) :
    (ModuleCat.ofHom (X := M) (Y := N) (f.hom.restrictScalars R)) ≫
        (restrictScalarsIsoOfScalarTower R S N).hom =
      (restrictScalarsIsoOfScalarTower R S M).hom ≫
        (restrictScalars (algebraMap R S)).map f := by
  ext x
  rfl

/-- The inverse comparisons commute with the same genuine restricted maps. -/
theorem restrictScalarsIsoOfScalarTower_inv_naturality
    {M N : ModuleCat.{m} R}
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (f : ModuleCat.of S M ⟶ ModuleCat.of S N) :
    (restrictScalars (algebraMap R S)).map f ≫
        (restrictScalarsIsoOfScalarTower R S N).inv =
      (restrictScalarsIsoOfScalarTower R S M).inv ≫
        (ModuleCat.ofHom (X := M) (Y := N) (f.hom.restrictScalars R)) := by
  ext x
  rfl

end ModuleCat
