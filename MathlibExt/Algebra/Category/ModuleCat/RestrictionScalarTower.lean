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
# Restriction of scalars along a module scalar tower

Let R be a commutative ring, S an R-algebra that is a ring, and M an R-module carrying an
S-module structure with IsScalarTower R S M. Then the given R-module is canonically isomorphic
to the restriction of the S-module along R → S. Both directions preserve every element.

The comparisons are natural for S-linear maps and their restrictions to R-linear maps. The R,
S and module carrier universes are independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory

namespace ModuleCat

universe r s m

variable (R : Type r) (S : Type s) [CommRing R] [Ring S] [Algebra R S]

/-- The restriction isomorphism of an existing scalar tower.

For M with compatible R- and S-module structures, the identity on its carrier gives an
R-linear isomorphism from M to the restriction of ModuleCat.of S M along algebraMap R S. -/
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

/-- Elements under the forward scalar-tower comparison.

The forward restriction comparison sends x ∈ M to the same element x. -/
@[simp]
theorem restrictScalarsIsoOfScalarTower_hom_apply (M : ModuleCat.{m} R)
    [Module S M] [IsScalarTower R S M] (x : M) :
    (restrictScalarsIsoOfScalarTower R S M).hom x = x := rfl

/-- Elements under the inverse scalar-tower comparison.

The inverse comparison from the restricted S-module sends every element to itself in the given
R-module. -/
@[simp]
theorem restrictScalarsIsoOfScalarTower_inv_apply (M : ModuleCat.{m} R)
    [Module S M] [IsScalarTower R S M]
    (x : (restrictScalars (algebraMap R S)).obj (ModuleCat.of S M)) :
    (restrictScalarsIsoOfScalarTower R S M).inv x = x := rfl

/-- Naturality of the forward scalar-tower comparison.

For an S-linear map f : M → N between compatible scalar towers, the forward comparisons
commute with f restricted to R and with the categorical restriction-of-scalars map. -/
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

/-- Naturality of the inverse scalar-tower comparison.

The inverse comparisons commute with the same S-linear morphism restricted to the given
R-module structures. -/
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
