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

public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.Universe

/-!
# Inverse unitors of module tensors in larger universes

The inverse unitors insert the lifted unit scalar on the left or right.
These computation laws use the scoped tensor structure over the given ring
and retain the module carrier and its scalar action.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v

namespace ModuleCat.UniverseTensor

variable (R : Type u) [CommRing R]

theorem leftUnitor_inv_apply (X : ModuleCat.{max u v} R) (x : X) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := monoidalLinear.{u,v} (R := R)
    (λ_ X).inv.hom x = (ULift.up (1 : R) : ULift.{v} R) ⊗ₜ[R] x := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := monoidalLinear.{u,v} (R := R)
  apply (λ_ X).toLinearEquiv.injective
  have hx := congrArg (fun f => f.hom x) (λ_ X).inv_hom_id
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at hx
  change (λ_ X).hom.hom ((λ_ X).inv.hom x) = (λ_ X).hom.hom (ULift.up (1 : R) ⊗ₜ[R] x)
  rw [leftUnitor_tmul, one_smul]
  exact hx

theorem rightUnitor_inv_apply (X : ModuleCat.{max u v} R) (x : X) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := monoidalLinear.{u,v} (R := R)
    (ρ_ X).inv.hom x = x ⊗ₜ[R] (ULift.up (1 : R) : ULift.{v} R) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := monoidalLinear.{u,v} (R := R)
  apply (ρ_ X).toLinearEquiv.injective
  have hx := congrArg (fun f => f.hom x) (ρ_ X).inv_hom_id
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at hx
  change (ρ_ X).hom.hom ((ρ_ X).inv.hom x) = (ρ_ X).hom.hom (x ⊗ₜ[R] ULift.up (1 : R))
  rw [rightUnitor_tmul, one_smul]
  exact hx

end ModuleCat.UniverseTensor
