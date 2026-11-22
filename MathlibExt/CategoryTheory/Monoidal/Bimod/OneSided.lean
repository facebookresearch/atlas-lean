/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.Free
public import MathlibExt.CategoryTheory.Monoidal.Bimod.Limits

/-!
# The original one-sided modules of a bimodule

Forgetting either action retains the literal carrier and the other original
action. The free bimodule becomes a free right module on its left tensor
coefficient. These functors will be used with the original generating cells
and the one-sided regular-module computation of derived units.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory MonoidalCategory MonoidalOpposite MonObj
open scoped MonoidalCategory

namespace Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B : Mon C}

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

/-- The original left module, with no change of carrier or left action. -/
def toLeftModule (M : Bimod A B) : Mod C A.X where
  X := M.X
  mod :=
    { smul := M.actLeft
      one_smul := M.one_actLeft
      mul_smul := M.left_assoc }

/-- The original right module, with no change of carrier or right action. -/
def toRightModule (M : Bimod A B) : RightModuleFree.Carrier B.X where
  X := M.X
  mod :=
    { smul := M.actRight
      one_smul := M.actRight_one
      mul_smul := M.right_assoc }

/-- Forgetting the right action retains every original left-module map. -/
def leftModuleFunctor (A B : Mon C) : Bimod A B ⥤ Mod C A.X where
  obj := toLeftModule
  map f := Mod.Hom.mk' f.hom f.left_act_hom
  map_id _ := by apply Mod.hom_ext; rfl
  map_comp _ _ := by apply Mod.hom_ext; rfl

/-- Forgetting the left action retains every original right-module map. -/
def rightModuleFunctor (A B : Mon C) : Bimod A B ⥤ RightModuleFree.Carrier B.X where
  obj := toRightModule
  map f := Mod.Hom.mk' f.hom f.right_act_hom
  map_id _ := by apply Mod.hom_ext; rfl
  map_comp _ _ := by apply Mod.hom_ext; rfl

/-- The complete left one-sided forgetful functor is the original bimodule forgetful functor. -/
theorem leftModuleFunctor_forget (A B : Mon C) :
    leftModuleFunctor A B ⋙ Mod.forget A.X = forget (B := B) A := rfl

/-- The complete right one-sided forgetful functor is the same original bimodule forgetful functor. -/
theorem rightModuleFunctor_forget (A B : Mon C) :
    rightModuleFunctor A B ⋙ Mod.forget (D := C) (mop B.X) = forget (B := B) A := rfl

/-- Forgetting the left free action leaves the actual free right module on the left coefficient. -/
theorem toRightModule_freeObject (A B : Mon C) (X : C) :
    toRightModule (freeObject A B X) = RightModuleFree.freeObject B.X (A.X ⊗ X) := rfl

/-- Every original free bimodule map has the same free right-module image. -/
theorem rightModuleFunctor_freeMap (A B : Mon C) {X Y : C} (f : X ⟶ Y) :
    (rightModuleFunctor A B).map ((free A B).map f) =
      RightModuleFree.freeMap B.X (A.X ◁ f) := rfl

/-- The whole free bimodule functor retains its original one-sided free presentation. -/
theorem free_rightModuleFunctor (A B : Mon C) :
    free A B ⋙ rightModuleFunctor A B = tensorLeft A.X ⋙ RightModuleFree.functor B.X := rfl

/-- Forgetting the right action gives the actual free left module through its original associator. -/
def freeLeftModuleIso (A B : Mon C) (X : C) :
    toLeftModule (freeObject A B X) ≅ (Mod.free A.X).obj (X ⊗ B.X) := by
  let M := toLeftModule (freeObject A B X)
  let N := (Mod.free A.X).obj (X ⊗ B.X)
  let e : M.X ≅ N.X := α_ A.X X B.X
  letI : ModObj A.X M.X := M.mod
  letI : ModObj A.X N.X := N.mod
  letI : IsModHom A.X e.hom := by
    constructor
    change (((𝟙 A.X ⊗ₘ (α_ A.X X B.X).hom) ≫ N.mod.smul ≫
      (α_ A.X X B.X).inv) ≫ (α_ A.X X B.X).hom) =
        (A.X ◁ (α_ A.X X B.X).hom) ≫ N.mod.smul
    simp only [id_tensorHom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact
    { hom := ⟨e.hom⟩
      inv := ⟨e.inv⟩
      hom_inv_id := by apply Mod.hom_ext; exact e.hom_inv_id
      inv_hom_id := by apply Mod.hom_ext; exact e.inv_hom_id }

/-- The complete forward free-left comparison is the original associator. -/
theorem freeLeftModuleIso_hom (A B : Mon C) (X : C) :
    ((freeLeftModuleIso A B X).hom).hom = (α_ A.X X B.X).hom := rfl

/-- The complete free-left presentation is natural in every original coefficient map. -/
def freeLeftModuleNatIso (A B : Mon C) :
    free A B ⋙ leftModuleFunctor A B ≅ tensorRight B.X ⋙ Mod.free A.X :=
  NatIso.ofComponents (freeLeftModuleIso A B) (by
    intro X Y f
    apply Mod.hom_ext
    change ((A.X ◁ f) ▷ B.X) ≫ (α_ A.X Y B.X).hom =
      (α_ A.X X B.X).hom ≫ (A.X ◁ (f ▷ B.X))
    exact associator_naturality_middle A.X f B.X)

/-- The original regular bimodule has the usual one-sided regular left module. -/
theorem toLeftModule_regular (A : Mon C) : toLeftModule (regular A) = Mod.regular A.X := rfl

end Bimod
