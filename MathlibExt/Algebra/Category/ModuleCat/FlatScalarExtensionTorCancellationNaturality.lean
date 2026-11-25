/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.FlatScalarExtensionTorCancellationUniverse

/-!
# Coefficient naturality of the original scalar tensor cancellation

The existing canonical cancellation commutes with every actual map of
the extended-ring coefficient module. Both original ring universes and
the original coefficient carrier are retained. The proof compares the
actual tensor maps on pure tensors and uses coefficient-map linearity.
No flatness hypothesis is needed.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor

universe u v w

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]

/-- The original scalar cancellation commutes with every actual
extended-ring coefficient map, in the original base module category. -/
theorem scalarTensorCancellationIso_hom_naturality_coefficient
    (f : R →+* S) {N₁ N₂ : ModuleCat.{max u v w} S} (g : N₁ ⟶ N₂)
    (X : ModuleCat.{max u v w} R) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.tensorStructure.{v,max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalCategory.{v,max u w}
    (restrictScalars.{max u v w,u,v} f).map
        (g ▷ (extendScalars.{u,v,max u v w} f).obj X) ≫
        (scalarTensorCancellationIso.{u,v,w} R S f N₂ X).hom =
      (scalarTensorCancellationIso.{u,v,w} R S f N₁ X).hom ≫
        ((restrictScalars.{max u v w,u,v} f).map g ▷ X) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,max v w}
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.tensorStructure.{v,max u w}
  let : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,max v w}
  let : MonoidalCategory (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalCategory.{v,max u w}
  let : Algebra R S := f.toAlgebra
  let : Module R N₁ := Module.compHom N₁ f
  let : Module R N₂ := Module.compHom N₂ f
  let : IsScalarTower R S N₁ := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower R S N₂ := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  apply ModuleCat.hom_ext
  change
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N₂ X).restrictScalars R).toLinearMap ∘ₗ
        (g.hom.rTensor (S ⊗[R] X)).restrictScalars R =
      TensorProduct.map (g.hom.restrictScalars R) LinearMap.id ∘ₗ
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N₁ X).restrictScalars R).toLinearMap
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => simp only [LinearMap.comp_apply, _root_.map_add, h₁, h₂]
  | tmul n sx =>
    induction sx using TensorProduct.inductionOn with
    | add sx sy hx hy =>
      simp only [LinearMap.comp_apply, TensorProduct.tmul_add, _root_.map_add, hx, hy]
    | tmul s x =>
      change TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N₂ X
          (g.hom n ⊗ₜ[S] (s ⊗ₜ[R] x)) =
        TensorProduct.map (g.hom.restrictScalars R) LinearMap.id
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N₁ X
            (n ⊗ₜ[S] (s ⊗ₜ[R] x)))
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.map_tmul]
      change (s • g.hom n) ⊗ₜ[R] x = g.hom (s • n) ⊗ₜ[R] x
      rw [g.hom.map_smul]

/-- The actual inverse cancellation preserves the same coefficient map. -/
theorem scalarTensorCancellationIso_inv_naturality_coefficient
    (f : R →+* S) {N₁ N₂ : ModuleCat.{max u v w} S} (g : N₁ ⟶ N₂)
    (X : ModuleCat.{max u v w} R) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,max v w}
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.tensorStructure.{v,max u w}
    letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,max v w}
    letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalCategory.{v,max u w}
    ((restrictScalars.{max u v w,u,v} f).map g ▷ X) ≫
        (scalarTensorCancellationIso.{u,v,w} R S f N₂ X).inv =
      (scalarTensorCancellationIso.{u,v,w} R S f N₁ X).inv ≫
        (restrictScalars.{max u v w,u,v} f).map
          (g ▷ (extendScalars.{u,v,max u v w} f).obj X) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,max v w}
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.tensorStructure.{v,max u w}
  let : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,max v w}
  let : MonoidalCategory (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalCategory.{v,max u w}
  rw [← cancel_mono (scalarTensorCancellationIso.{u,v,w} R S f N₂ X).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [scalarTensorCancellationIso_hom_naturality_coefficient.{u,v,w} R S f g X,
    Iso.inv_hom_id_assoc]

end ModuleCat.UniverseTensor
