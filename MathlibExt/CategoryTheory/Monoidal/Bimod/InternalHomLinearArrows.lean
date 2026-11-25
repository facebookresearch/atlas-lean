/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.InternalHom
public import MathlibExt.CategoryTheory.Monoidal.Bimod.RightFree
public import MathlibExt.CategoryTheory.Monoidal.Mod.RightTensorHomPreMap

/-!
# The two actual bimodule arrows imposing right scalar linearity

The source right action induces precomposition on the mapping bimodule.
The target right action induces a second arrow by the actual right tensor
adjunction. Both arrows preserve both outer actions. Their equalizer will
therefore carry the original target and source scalar actions.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory MonoidalCategory MonoidalOpposite MonObj
open CategoryTheory.HomogeneousLocalization
open scoped MonoidalCategory

namespace CategoryTheory.Mod.RightLeftTensor

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {B : C} [MonObj B]

/-- A balanced original pairing remains balanced after right tensor extension and postcomposition. -/
theorem tensorRight_balance (M : RightModuleFree.Carrier B) (N : Mod C B)
    {X Y : C} (U : C) (k : M.X ⊗ N.X ⟶ X) (b : X ⊗ U ⟶ Y)
    (hk : (M.mod.smul ▷ N.X) ≫ k = (α_ M.X B N.X).hom ≫ (M.X ◁ N.mod.smul) ≫ k) :
    (M.mod.smul ▷ (N.X ⊗ U)) ≫ (α_ M.X N.X U).inv ≫ (k ▷ U) ≫ b =
      (α_ M.X B (N.X ⊗ U)).hom ≫
        (M.X ◁ (Mod.AmbientTensor.rightModule B U N).mod.smul) ≫
          (α_ M.X N.X U).inv ≫ (k ▷ U) ≫ b := by
  have ha : (α_ (M.X ⊗ B) N.X U).inv ≫ ((α_ M.X B N.X).hom ▷ U) =
      (α_ M.X B (N.X ⊗ U)).hom ≫ (M.X ◁ (α_ B N.X U).inv) ≫
        (α_ M.X (B ⊗ N.X) U).inv := by monoidal
  simp only [Mod.AmbientTensor.rightModule_smul, whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc, hk, comp_whiskerRight]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_middle_assoc]
  have h := congrArg (fun t => t ≫ ((M.X ◁ N.mod.smul) ▷ U) ≫ (k ▷ U) ≫ b) ha
  simp only [Category.assoc] at h
  exact h

end CategoryTheory.Mod.RightLeftTensor

namespace Bimod.InternalHom

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] {A B D : Mon C}

/-- Every original source bimodule map gives actual precomposition preserving both outer actions. -/
def unbalancedPre {N N' : Bimod B D} (f : N ⟶ N') (P : Bimod A D) :
    unbalanced N' P ⟶ unbalanced N P where
  hom := (MonoidalClosed.pre f.hom).app P.X
  left_act_hom := (AmbientTensorHom.preMap A.X f.hom (toLeftModule P)).isModHom.smul_hom
  right_act_hom := Mod.RightLeftTensor.rightHomPre_linear ((leftModuleFunctor B D).map f) P.X

/-- The entire bimodule source map is the original ambient internal-Hom pre-map. -/
theorem unbalancedPre_hom {N N' : Bimod B D} (f : N ⟶ N') (P : Bimod A D) :
    (unbalancedPre f P).hom = (MonoidalClosed.pre f.hom).app P.X := rfl

/-- Every original target bimodule map gives actual postcomposition preserving both outer actions. -/
def unbalancedPost (N : Bimod B D) {P P' : Bimod A D} (f : P ⟶ P') :
    unbalanced N P ⟶ unbalanced N P' where
  hom := (ihom N.X).map f.hom
  left_act_hom := (AmbientTensorHom.cotensorMap A.X N.X ((leftModuleFunctor A D).map f)).isModHom.smul_hom
  right_act_hom := ((Mod.RightLeftTensor.rightHomFunctor (toLeftModule N)).map f.hom).isModHom.smul_hom

/-- The entire target map is the original ambient internal-Hom map. -/
theorem unbalancedPost_hom (N : Bimod B D) {P P' : Bimod A D} (f : P ⟶ P') :
    (unbalancedPost N f).hom = (ihom N.X).map f.hom := rfl

/-- Precomposition by the actual source right action is the first D-linearity arrow. -/
def rightLinearityPre (N : Bimod B D) (P : Bimod A D) :
    unbalanced N P ⟶ unbalanced (rightFreeObject B D (toLeftModule N)) P :=
  unbalancedPre (rightFreeCounit N) P

/-- The complete first arrow is precomposition by the original right scalar action. -/
theorem rightLinearityPre_hom (N : Bimod B D) (P : Bimod A D) :
    (rightLinearityPre N P).hom = (MonoidalClosed.pre N.actRight).app P.X := rfl

/-- The actual target action is transposed inside the original A-module tensor adjunction. -/
def rightLinearityPostLeft (N : Bimod B D) (P : Bimod A D) :
    leftModule N P ⟶ leftModule (rightFreeObject B D (toLeftModule N)) P :=
  ((ambientRightAdjunction A (N.X ⊗ D.X)).homEquiv (leftModule N P) (toLeftModule P))
    ((Mod.AmbientTensor.rightAssociateIso A.X N.X D.X (leftModule N P)).inv ≫
      Mod.AmbientTensor.rightMap A.X (𝟙 D.X)
        ((ambientRightAdjunction A N.X).counit.app (toLeftModule P)) ≫
          rightActionLeftMap P)

/-- Its entire carrier is the original right curry of evaluation followed by the target action. -/
theorem rightLinearityPostLeft_hom (N : Bimod B D) (P : Bimod A D) :
    (rightLinearityPostLeft N P).hom =
      (originalRightTensorAdjunction (N.X ⊗ D.X)).homEquiv ((ihom N.X).obj P.X) P.X
        ((α_ ((ihom N.X).obj P.X) N.X D.X).inv ≫
          ((originalRightTensorAdjunction N.X).counit.app P.X ▷ D.X) ≫ P.actRight) := by
  rw [rightLinearityPostLeft, ambientRightAdjunction_homEquiv]
  simp only [Mod.comp_hom', Mod.AmbientTensor.rightAssociateIso_inv, Mod.AmbientTensor.rightMap_hom,
    tensorHom_id, ambientRightAdjunction_counit_hom, rightActionLeftMap_hom]
  rfl

/-- Right currying of the original evaluation/action word also preserves the source B action. -/
theorem rightLinearityPostLeft_right_linear (N : Bimod B D) (P : Bimod A D) :
    (unbalanced N P).actRight ≫ (rightLinearityPostLeft N P).hom =
      ((rightLinearityPostLeft N P).hom ▷ B.X) ≫
        (unbalanced (rightFreeObject B D (toLeftModule N)) P).actRight := by
  let R := rightModule N P
  let E := toLeftModule (rightFreeObject B D (toLeftModule N))
  let e := (originalRightTensorAdjunction N.X).counit.app P.X
  let k := (α_ R.X N.X D.X).inv ≫ (e ▷ D.X) ≫ P.actRight
  have hbal := Mod.RightLeftTensor.tensorRight_balance R (toLeftModule N) D.X e P.actRight
    (Mod.RightLeftTensor.rightEvaluation_balance (toLeftModule N) P.X)
  have hlin := (Mod.RightLeftTensor.rightCurry_linear_iff R E k).mpr hbal
  rw [rightLinearityPostLeft_hom]
  exact hlin

/-- Postcomposition by the original target right action is the second actual bimodule arrow. -/
def rightLinearityPost (N : Bimod B D) (P : Bimod A D) :
    unbalanced N P ⟶ unbalanced (rightFreeObject B D (toLeftModule N)) P where
  hom := (rightLinearityPostLeft N P).hom
  left_act_hom := (rightLinearityPostLeft N P).isModHom.smul_hom
  right_act_hom := rightLinearityPostLeft_right_linear N P

/-- The complete second arrow is the literal right-curry evaluation/action word. -/
theorem rightLinearityPost_hom (N : Bimod B D) (P : Bimod A D) :
    (rightLinearityPost N P).hom =
      (originalRightTensorAdjunction (N.X ⊗ D.X)).homEquiv ((ihom N.X).obj P.X) P.X
        ((α_ ((ihom N.X).obj P.X) N.X D.X).inv ≫
          ((originalRightTensorAdjunction N.X).counit.app P.X ▷ D.X) ≫ P.actRight) :=
  rightLinearityPostLeft_hom N P

end Bimod.InternalHom
