/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.HomogeneousLocalization.AmbientTensorHom
import MathlibExt.CategoryTheory.Monoidal.Mod.ExtensionOfScalarsCoherence

/-!
# Original ambient actions and actual scalar restriction

The actual scalar restriction along the original associative monoid map
commutes with the original ambient tensor and cotensor actions. Both
comparisons retain the literal underlying identity and every original
coordinate and target-module map. The proofs use the original coefficient
map and braiding naturality, without coefficient commutativity or a
localized/derived-action outcome premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory MonObj
open CategoryTheory.Mod.ExtensionOfScalars
open scoped CategoryTheory.MonObj

namespace CategoryTheory.HomogeneousLocalization.ScalarActionTransport

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]
  {A B : C} [MonObj A] [MonObj B] (p : A ⟶ B) [IsMonHom p]

/-- The original cotensor action retains the exact original restricted coefficient action. -/
theorem cotensor_smul (U : C) (N : Mod C B) :
    (AmbientTensorHom.cotensorModule A U ((restriction p).obj N)).mod.smul =
      (p ▷ (ihom U).obj N.X) ≫ (AmbientTensorHom.cotensorModule B U N).mod.smul := by
  let H := (ihom U).obj N.X
  let qA : U ⊗ (A ⊗ H) ⟶ N.X := (α_ U A H).inv ≫
    ((β_ U A).hom ▷ H) ≫ (α_ A U H).hom ≫
    (A ◁ (ihom.ev U).app N.X) ≫ (p ▷ N.X) ≫ N.mod.smul
  let qB : U ⊗ (B ⊗ H) ⟶ N.X := (α_ U B H).inv ≫
    ((β_ U B).hom ▷ H) ≫ (α_ B U H).hom ≫
    (B ◁ (ihom.ev U).app N.X) ≫ N.mod.smul
  change MonoidalClosed.curry qA = (p ▷ H) ≫ MonoidalClosed.curry qB
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  dsimp only [qA, qB]
  slice_rhs 1 2 => rw [associator_inv_naturality_middle]
  slice_rhs 2 3 => rw [← comp_whiskerRight, braiding_naturality_right, comp_whiskerRight]
  slice_rhs 3 4 => rw [associator_naturality_left]
  slice_rhs 4 5 => rw [← whisker_exchange]
  monoidal

/-- Both actual cotensor/restriction comparison maps are the original underlying identity. -/
def cotensorIso (U : C) (N : Mod C B) :
    AmbientTensorHom.cotensorModule A U ((restriction p).obj N) ≅
      (restriction p).obj (AmbientTensorHom.cotensorModule B U N) :=
  Mod.isoOfUnderlyingIso (Iso.refl ((ihom U).obj N.X)) (by
    change (AmbientTensorHom.cotensorModule A U ((restriction p).obj N)).mod.smul ≫ 𝟙 _ =
      (A ◁ 𝟙 _) ≫ ((p ▷ (ihom U).obj N.X) ≫ (AmbientTensorHom.cotensorModule B U N).mod.smul)
    simp only [Category.comp_id, whiskerLeft_id, Category.id_comp, cotensor_smul])

@[simp]
theorem cotensorIso_hom (U : C) (N : Mod C B) :
    (cotensorIso p U N).hom.hom = 𝟙 ((ihom U).obj N.X) := rfl

@[simp]
theorem cotensorIso_inv (U : C) (N : Mod C B) :
    (cotensorIso p U N).inv.hom = 𝟙 ((ihom U).obj N.X) := rfl

/-- Every original whole target-module map retains the actual cotensor scalar comparison. -/
def cotensorNatIso (U : C) :
    restriction p ⋙ AmbientTensorHom.rightFunctor A U ≅
      AmbientTensorHom.rightFunctor B U ⋙ restriction p :=
  NatIso.ofComponents (cotensorIso p U) (by
    intro N N' f
    apply Mod.hom_ext
    change (ihom U).map f.hom ≫ 𝟙 _ = 𝟙 _ ≫ (ihom U).map f.hom
    simp)

omit [MonoidalClosed C] in
/-- The original inverse-braid tensor action retains the exact original scalar restriction. -/
theorem tensor_smul (U : C) (N : Mod C B) :
    (Mod.AmbientTensor.tensorModule A U ((restriction p).obj N)).mod.smul =
      (p ▷ (U ⊗ N.X)) ≫ (Mod.AmbientTensor.tensorModule B U N).mod.smul := by
  rw [Mod.AmbientTensor.module_smul, Mod.AmbientTensor.module_smul]
  change (α_ A U N.X).inv ≫ ((β_ U A).inv ▷ N.X) ≫ (α_ U A N.X).hom ≫
      (U ◁ ((p ▷ N.X) ≫ N.mod.smul)) =
    (p ▷ (U ⊗ N.X)) ≫ (α_ B U N.X).inv ≫ ((β_ U B).inv ▷ N.X) ≫
      (α_ U B N.X).hom ≫ (U ◁ N.mod.smul)
  slice_rhs 1 2 => rw [associator_inv_naturality_left]
  slice_rhs 2 3 => rw [← comp_whiskerRight, braiding_inv_naturality_left, comp_whiskerRight]
  slice_rhs 3 4 => rw [associator_naturality_middle]
  simp only [whiskerLeft_comp, Category.assoc]

/-- The original tensor/restriction comparison keeps both full module maps of the underlying identity. -/
def tensorIso (U : C) (N : Mod C B) :
    Mod.AmbientTensor.tensorModule A U ((restriction p).obj N) ≅
      (restriction p).obj (Mod.AmbientTensor.tensorModule B U N) :=
  Mod.isoOfUnderlyingIso (Iso.refl (U ⊗ N.X)) (by
    change (Mod.AmbientTensor.tensorModule A U ((restriction p).obj N)).mod.smul ≫ 𝟙 _ =
      (A ◁ 𝟙 _) ≫ ((p ▷ (U ⊗ N.X)) ≫ (Mod.AmbientTensor.tensorModule B U N).mod.smul)
    simp only [Category.comp_id, whiskerLeft_id, Category.id_comp, tensor_smul])

omit [MonoidalClosed C] in
@[simp]
theorem tensorIso_hom (U : C) (N : Mod C B) : (tensorIso p U N).hom.hom = 𝟙 (U ⊗ N.X) := rfl

omit [MonoidalClosed C] in
@[simp]
theorem tensorIso_inv (U : C) (N : Mod C B) : (tensorIso p U N).inv.hom = 𝟙 (U ⊗ N.X) := rfl

/-- Every original whole target-module arrow keeps the actual tensor scalar comparison. -/
def tensorNatIso (U : C) :
    restriction p ⋙ Mod.AmbientTensor.functor A U ≅ Mod.AmbientTensor.functor B U ⋙ restriction p :=
  NatIso.ofComponents (tensorIso p U) (by
    intro N N' f
    apply Mod.hom_ext
    simp only [Functor.comp_map, Mod.comp_hom', tensorIso_hom]
    rw [Mod.AmbientTensor.functor_map_hom]
    change (U ◁ f.hom) ≫ 𝟙 _ = 𝟙 _ ≫ ((Mod.AmbientTensor.functor B U).map f).hom
    rw [Mod.AmbientTensor.functor_map_hom]
    simp)

end CategoryTheory.HomogeneousLocalization.ScalarActionTransport
