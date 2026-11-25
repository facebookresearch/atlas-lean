/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductMonoidal

/-! # Tests for the scoped biproduct monoidal structure on a core -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.CategoryTheory.Limits.CoreBiproductMonoidal

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Importing the provider does not install its monoidal structure globally. -/
example : True := by
  fail_if_success
    let _ := (inferInstance : MonoidalCategoryStruct (Core C))
  trivial

open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory

#synth MonoidalCategoryStruct (Core C)
#synth MonoidalCategory (Core C)

#check coreBiprodTensorObj_of
#check coreBiprodTensorUnit_of
#check coreBiprodTensorHom_iso
#check coreBiprodTensorHom_iso_hom
#check coreBiprodAssociator_iso
#check coreBiprodLeftUnitor_iso
#check coreBiprodRightUnitor_iso
#check coreBiprodTensorLeft_obj_of
#check coreBiprodTensorLeft_map_iso_hom

example (X Y : Core C) :
    (X ⊗ Y).of = (X.of ⊞ Y.of : C) := by
  simp

example : (𝟙_ (Core C)).of = (0 : C) := by
  simp

example {X₁ Y₁ X₂ Y₂ : Core C}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).iso.hom = biprod.map f.iso.hom g.iso.hom := by
  simp

/-- Tensoring identities gives the identity core morphism. -/
example (X Y : Core C) :
    (𝟙 X ⊗ₘ 𝟙 Y) = 𝟙 (X ⊗ Y) := by
  simp

/-- Tensor maps preserve composition in both variables. -/
example {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Core C}
    (f₁ : X₁ ⟶ Y₁) (g₁ : Y₁ ⟶ Z₁)
    (f₂ : X₂ ⟶ Y₂) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) =
      (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by
  simp

example (X Y Z : Core C) :
    ((α_ X Y Z).hom).iso = biprod.associator X.of Y.of Z.of := by
  simp

example (X : Core C) :
    ((λ_ X).hom).iso =
      (isoZeroBiprod (isZero_zero C)).symm := by
  simp

example (X : Core C) :
    ((ρ_ X).hom).iso =
      (isoBiprodZero (isZero_zero C)).symm := by
  simp

/-- The monoidal triangle is available to downstream consumers. -/
example (X Y : Core C) :
    (α_ X (𝟙_ (Core C)) Y).hom ≫ X ◁ (λ_ Y).hom =
      (ρ_ X).hom ▷ Y :=
  MonoidalCategory.triangle X Y

/-- The monoidal pentagon is available to downstream consumers. -/
example (W X Y Z : Core C) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫
        W ◁ (α_ X Y Z).hom =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom :=
  MonoidalCategory.pentagon W X Y Z

example (A X : Core C) :
    ((MonoidalCategory.tensorLeft A).obj X).of =
      ((coreLeftBiprodFunctor A.of).obj X).of := by
  simp

example (A : Core C) {X Y : Core C} (f : X ⟶ Y) :
    (((MonoidalCategory.tensorLeft A).map f).iso.hom) =
      (((coreLeftBiprodFunctor A.of).map f).iso.hom) :=
  coreBiprodTensorLeft_map_iso_hom A f

private abbrev ZeroModuleCat := ModuleCat (ZMod 1)

/-- Boundary case: the scoped instance is available for a zero category. -/
example : MonoidalCategory (Core ZeroModuleCat) :=
  inferInstance

example (X : Core ZeroModuleCat) :
    (X ⊗ (⟨(0 : ZeroModuleCat)⟩ : Core ZeroModuleCat)).of =
      (X.of ⊞ (0 : ZeroModuleCat) : ZeroModuleCat) := by
  simp

#print axioms CoreBiprodMonoidal.monoidalCategoryStruct
#print axioms CoreBiprodMonoidal.monoidalCategory
#print axioms coreBiprodTensorObj_of
#print axioms coreBiprodTensorHom_iso_hom
#print axioms coreBiprodAssociator_iso
#print axioms coreBiprodTensorLeft_map_iso_hom

end MathlibExtTest.CategoryTheory.Limits.CoreBiproductMonoidal

end
