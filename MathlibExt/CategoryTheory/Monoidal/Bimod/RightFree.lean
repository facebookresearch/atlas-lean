/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.OneSided
public import MathlibExt.CategoryTheory.Monoidal.Mod.AmbientTensor

/-!
# Free right actions on original left modules

The free right `D` action on a left `B` module has carrier `N.X ⊗ D.X`.
The left action is the existing ambient right tensor action, and the right
action is the existing free right-module multiplication. Their commuting
law and the complete free/forget adjunction are proved on these maps.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory MonoidalCategory MonoidalOpposite MonObj
open scoped MonoidalCategory

namespace Bimod

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original right action is a morphism for the independent original left action. -/
def rightActionLeftMap {B D : Mon C} (N : Bimod B D) :
    Mod.AmbientTensor.rightModule B.X D.X (toLeftModule N) ⟶ toLeftModule N :=
  Mod.Hom.mk' N.actRight (by
    change ((α_ B.X N.X D.X).inv ≫ (N.actLeft ▷ D.X)) ≫ N.actRight =
      (B.X ◁ N.actRight) ≫ N.actLeft
    rw [Category.assoc, N.middle_assoc, Iso.inv_hom_id_assoc])

/-- Its complete underlying map is the actual original right scalar action. -/
theorem rightActionLeftMap_hom {B D : Mon C} (N : Bimod B D) :
    (rightActionLeftMap N).hom = N.actRight := rfl

/-- The original free right module with its existing commuting left tensor action. -/
@[reducible]
def rightFreeObject (B D : Mon C) (N : Mod C B.X) : Bimod B D := by
  let L := Mod.AmbientTensor.rightModule B.X D.X N
  let R := RightModuleFree.freeObject D.X N.X
  letI : ModObj B.X L.X := L.mod
  letI : ModObj (mop D.X) R.X := R.mod
  refine
    { X := N.X ⊗ D.X
      actLeft := L.mod.smul
      actRight := R.mod.smul
      one_actLeft := ModObj.one_smul_self B.X L.X
      left_assoc := ModObj.mul_smul_self B.X L.X
      actRight_one := ModObj.one_smul (M := mop D.X) R.X
      right_assoc := ModObj.mul_smul (M := mop D.X) R.X
      middle_assoc := ?_ }
  change (Mod.AmbientTensor.rightModule B.X D.X N).mod.smul ▷ D.X ≫ R.mod.smul =
    (α_ B.X (N.X ⊗ D.X) D.X).hom ≫ B.X ◁ R.mod.smul ≫
      (Mod.AmbientTensor.rightModule B.X D.X N).mod.smul
  have hr : R.mod.smul = (α_ N.X D.X D.X).hom ≫ N.X ◁ μ[D.X] := rfl
  rw [Mod.AmbientTensor.rightModule_smul, hr]
  exact tensorAction_commute B.X N.X D.X N.mod.smul μ[D.X]

/-- The free right carrier is the literal original two-factor tensor. -/
theorem rightFreeObject_X (B D : Mon C) (N : Mod C B.X) :
    (rightFreeObject B D N).X = N.X ⊗ D.X := rfl

/-- Its complete left action is the original ambient right tensor extension. -/
theorem rightFreeObject_actLeft (B D : Mon C) (N : Mod C B.X) :
    (rightFreeObject B D N).actLeft = (α_ B.X N.X D.X).inv ≫ N.mod.smul ▷ D.X := rfl

/-- Its complete right action uses the original right multiplication. -/
theorem rightFreeObject_actRight (B D : Mon C) (N : Mod C B.X) :
    (rightFreeObject B D N).actRight = (α_ N.X D.X D.X).hom ≫ N.X ◁ μ[D.X] := rfl

/-- Every original left-module map has its free right-module extension. -/
def rightFreeMap (B D : Mon C) {N N' : Mod C B.X} (f : N ⟶ N') :
    rightFreeObject B D N ⟶ rightFreeObject B D N' where
  hom := f.hom ▷ D.X
  left_act_hom := Mod.AmbientTensor.rightModule_map_linear B.X D.X f
  right_act_hom := (RightModuleFree.freeMap D.X f.hom).isModHom.smul_hom

/-- The entire free source map is the original right-whiskered module map. -/
theorem rightFreeMap_hom (B D : Mon C) {N N' : Mod C B.X} (f : N ⟶ N') :
    (rightFreeMap B D f).hom = f.hom ▷ D.X := rfl

/-- Free right scalar action is functorial on every original left module. -/
def rightFree (B D : Mon C) : Mod C B.X ⥤ Bimod B D where
  obj := rightFreeObject B D
  map := rightFreeMap B D
  map_id N := by
    apply hom_ext
    change 𝟙 N.X ▷ D.X = 𝟙 (N.X ⊗ D.X)
    exact id_whiskerRight _ _
  map_comp f g := by
    apply hom_ext
    exact comp_whiskerRight f.hom g.hom D.X

/-- The actual bimodule right action is the free-right counit, preserving both actions. -/
def rightFreeCounit {B D : Mon C} (N : Bimod B D) :
    rightFreeObject B D (toLeftModule N) ⟶ N where
  hom := N.actRight
  left_act_hom := (rightActionLeftMap N).isModHom.smul_hom
  right_act_hom := by
    change ((α_ N.X D.X D.X).hom ≫ N.X ◁ μ[D.X]) ≫ N.actRight =
      (N.actRight ▷ D.X) ≫ N.actRight
    rw [Category.assoc, N.right_assoc, Iso.hom_inv_id_assoc]

/-- Its entire carrier map is the original action, without a chosen comparison. -/
theorem rightFreeCounit_hom {B D : Mon C} (N : Bimod B D) :
    (rightFreeCounit N).hom = N.actRight := rfl

/-- The original counit is natural on every original bimodule arrow. -/
theorem rightFreeCounit_naturality {B D : Mon C} {N N' : Bimod B D} (f : N ⟶ N') :
    rightFreeMap B D ((leftModuleFunctor B D).map f) ≫ rightFreeCounit N' =
      rightFreeCounit N ≫ f := by
  apply hom_ext
  exact f.right_act_hom.symm

/-- The existing tensor unit comparison and scalar unit give the free right generator as a left-module map. -/
def rightFreeGenerator (B D : Mon C) (N : Mod C B.X) :
    N ⟶ toLeftModule (rightFreeObject B D N) :=
  (Mod.AmbientTensor.rightUnitIso B.X N).inv ≫ Mod.AmbientTensor.rightMap B.X η[D.X] (𝟙 N)

/-- The generator retains the original right unitor and scalar unit insertion. -/
theorem rightFreeGenerator_hom (B D : Mon C) (N : Mod C B.X) :
    (rightFreeGenerator B D N).hom = RightModuleFree.freeGenerator D.X N.X := by
  rw [rightFreeGenerator, Mod.comp_hom', Mod.AmbientTensor.rightUnitIso_inv,
    Mod.AmbientTensor.rightMap_hom, Mod.id_hom', id_tensorHom]
  rfl

/-- Extend an original left-module map using the actual target right action. -/
def rightFreeExtend (B D : Mon C) (N : Mod C B.X) (P : Bimod B D)
    (f : N ⟶ toLeftModule P) : rightFreeObject B D N ⟶ P := by
  let r := RightModuleFree.extendFree D.X N.X (toRightModule P) f.hom
  refine
    { hom := r.hom
      left_act_hom := ?_
      right_act_hom := r.isModHom.smul_hom }
  have hr : r.hom = (f.hom ▷ D.X) ≫ P.actRight :=
    congrFun (RightModuleFree.extendFree_hom D.X N.X (toRightModule P)) f.hom
  have h := (Mod.AmbientTensor.rightMap B.X (𝟙 D.X) f ≫ rightActionLeftMap P).isModHom.smul_hom
  rw [Mod.comp_hom', Mod.AmbientTensor.rightMap_hom, tensorHom_id, rightActionLeftMap_hom] at h
  rw [hr]
  exact h

/-- The full extension carrier is the original tensored map followed by the right action. -/
theorem rightFreeExtend_hom (B D : Mon C) (N : Mod C B.X) (P : Bimod B D)
    (f : N ⟶ toLeftModule P) :
    (rightFreeExtend B D N P f).hom = (f.hom ▷ D.X) ≫ P.actRight :=
  congrFun (RightModuleFree.extendFree_hom D.X N.X (toRightModule P)) f.hom

/-- The complete free right bimodule Hom function uses the original generator and selected extension. -/
def rightFreeHomEquiv (B D : Mon C) (N : Mod C B.X) (P : Bimod B D) :
    (rightFreeObject B D N ⟶ P) ≃ (N ⟶ toLeftModule P) where
  toFun f := rightFreeGenerator B D N ≫ (leftModuleFunctor B D).map f
  invFun := rightFreeExtend B D N P
  left_inv f := by
    apply hom_ext
    have h := congrArg Mod.Hom.hom
      (RightModuleFree.extendFree_generator D.X N.X (toRightModule P)
        ((rightModuleFunctor B D).map f))
    change (RightModuleFree.extendFree D.X N.X (toRightModule P)
      ((rightFreeGenerator B D N ≫ (leftModuleFunctor B D).map f).hom)).hom = f.hom
    rw [Mod.comp_hom', rightFreeGenerator_hom]
    exact h
  right_inv f := by
    apply Mod.hom_ext
    change (rightFreeGenerator B D N).hom ≫ (rightFreeExtend B D N P f).hom = f.hom
    rw [rightFreeGenerator_hom]
    exact RightModuleFree.freeGenerator_extend D.X N.X (toRightModule P) f.hom

/-- The free right action and the original one-sided forgetful functor form the complete adjunction. -/
def rightFreeForgetAdjunction (B D : Mon C) : rightFree B D ⊣ leftModuleFunctor B D :=
  Adjunction.mkOfHomEquiv
    { homEquiv := rightFreeHomEquiv B D
      homEquiv_naturality_left_symm := by
        intro N' N P f g
        apply hom_ext
        exact congrArg Mod.Hom.hom
          (RightModuleFree.freeHomEquiv_naturality_left D.X f.hom (toRightModule P) g.hom)
      homEquiv_naturality_right := by
        intro N P P' f g
        apply Mod.hom_ext
        change (rightFreeGenerator B D N).hom ≫ (f.hom ≫ g.hom) =
          ((rightFreeGenerator B D N).hom ≫ f.hom) ≫ g.hom
        exact (Category.assoc _ _ _).symm }

end Bimod
