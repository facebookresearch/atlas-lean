/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductPentagon

/-!
# The scoped biproduct monoidal structure on a core

The core of a category with chosen binary biproducts and a chosen zero object
has a monoidal structure whose tensor is the chosen biproduct and whose unit is
the chosen zero object.  Tensor maps are defined explicitly with
`biprod.mapIso`, so parameter naturality remains visible without expanding a
composite of two whiskerings.

The instances are scoped: importing this file does not globally choose this
monoidal structure on `Core C`.  This file adds no braiding, action, or
construction specific to Quillen Q or S⁻¹S.
-/

@[expose] public section

noncomputable section

open CategoryTheory ZeroObject

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

namespace CoreBiprodMonoidal

/-- The data of the chosen biproduct monoidal structure on `Core C`.

This is scoped so that importing the file does not globally choose a monoidal
structure on the core. -/
noncomputable scoped instance monoidalCategoryStruct :
    MonoidalCategoryStruct (Core C) where
  tensorObj X Y := ⟨X.of ⊞ Y.of⟩
  whiskerLeft X _ _ g :=
    (Core.isoMk (biprod.mapIso (Iso.refl X.of) g.iso)).hom
  whiskerRight f Y :=
    (Core.isoMk (biprod.mapIso f.iso (Iso.refl Y.of))).hom
  tensorHom f g :=
    (Core.isoMk (biprod.mapIso f.iso g.iso)).hom
  tensorUnit := ⟨(0 : C)⟩
  associator X Y Z :=
    Core.isoMk (biprod.associator X.of Y.of Z.of)
  leftUnitor X :=
    Core.isoMk
      (isoZeroBiprod (X := (0 : C)) (Y := X.of) (isZero_zero C)).symm
  rightUnitor X :=
    Core.isoMk
      (isoBiprodZero (X := X.of) (Y := (0 : C)) (isZero_zero C)).symm

open scoped MonoidalCategory

/-- The lawful chosen biproduct monoidal structure on `Core C`. -/
noncomputable scoped instance monoidalCategory : MonoidalCategory (Core C) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by
      intro X Y
      apply Core.hom_ext
      change biprod.map (𝟙 X.of) (𝟙 Y.of) = 𝟙 (X.of ⊞ Y.of)
      apply biprod.hom_ext <;> simp)
    (id_tensorHom := by
      intro X Y₁ Y₂ f
      rfl)
    (tensorHom_id := by
      intro X₁ X₂ f Y
      rfl)
    (tensorHom_comp_tensorHom := by
      intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
      apply Core.hom_ext
      change
        biprod.map f₁.iso.hom f₂.iso.hom ≫
            biprod.map g₁.iso.hom g₂.iso.hom =
          biprod.map (f₁.iso.hom ≫ g₁.iso.hom)
            (f₂.iso.hom ≫ g₂.iso.hom)
      apply biprod.hom_ext <;> simp [Category.assoc])
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      apply Core.hom_ext
      exact biprod.associator_natural f₁.iso.hom f₂.iso.hom f₃.iso.hom)
    (leftUnitor_naturality := by
      intro X Y f
      apply Core.hom_ext
      exact biprod.map_snd (𝟙 (0 : C)) f.iso.hom)
    (rightUnitor_naturality := by
      intro X Y f
      apply Core.hom_ext
      exact biprod.map_fst f.iso.hom (𝟙 (0 : C)))
    (pentagon := by
      intro W X Y Z
      apply Core.hom_ext
      exact
        (coreLeftBiprodBiprodIso_pentagon_component
          W.of X.of Y.of Z.of).symm)
    (triangle := by
      intro X Y
      apply Core.hom_ext
      exact coreLeftBiprodBiprodIso_rightUnit_component X.of Y.of)

end CoreBiprodMonoidal

open scoped CoreBiprodMonoidal MonoidalCategory

/-- The underlying object of the tensor is the chosen biproduct. -/
@[simp]
theorem coreBiprodTensorObj_of (X Y : Core C) :
    (X ⊗ Y).of = (X.of ⊞ Y.of : C) :=
  rfl

/-- The underlying object of the tensor unit is the chosen zero object. -/
@[simp]
theorem coreBiprodTensorUnit_of :
    (𝟙_ (Core C)).of = (0 : C) :=
  rfl

/-- The isomorphism underlying a tensor map is the chosen biproduct map
isomorphism. -/
@[simp]
theorem coreBiprodTensorHom_iso
    {X₁ Y₁ X₂ Y₂ : Core C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).iso = biprod.mapIso f.iso g.iso :=
  rfl

/-- The forward map underlying a tensor map is `biprod.map`. -/
theorem coreBiprodTensorHom_iso_hom
    {X₁ Y₁ X₂ Y₂ : Core C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).iso.hom = biprod.map f.iso.hom g.iso.hom :=
  rfl

/-- The associator is induced by the chosen biproduct associator. -/
@[simp]
theorem coreBiprodAssociator_iso (X Y Z : Core C) :
    ((α_ X Y Z).hom).iso = biprod.associator X.of Y.of Z.of :=
  rfl

/-- The left unitor is induced by the inverse zero-biproduct isomorphism. -/
@[simp]
theorem coreBiprodLeftUnitor_iso (X : Core C) :
    ((λ_ X).hom).iso = (isoZeroBiprod (isZero_zero C)).symm :=
  rfl

/-- The right unitor is induced by the inverse biproduct-zero isomorphism. -/
@[simp]
theorem coreBiprodRightUnitor_iso (X : Core C) :
    ((ρ_ X).hom).iso = (isoBiprodZero (isZero_zero C)).symm :=
  rfl

/-- Left tensoring and `coreLeftBiprodFunctor` agree on underlying objects. -/
@[simp]
theorem coreBiprodTensorLeft_obj_of (A X : Core C) :
    ((MonoidalCategory.tensorLeft A).obj X).of =
      ((coreLeftBiprodFunctor A.of).obj X).of :=
  rfl

/-- Left tensoring and `coreLeftBiprodFunctor` agree on underlying forward
maps. -/
theorem coreBiprodTensorLeft_map_iso_hom
    (A : Core C) {X Y : Core C} (f : X ⟶ Y) :
    (((MonoidalCategory.tensorLeft A).map f).iso.hom) =
      (((coreLeftBiprodFunctor A.of).map f).iso.hom) :=
  rfl

end CategoryTheory.Limits

end
