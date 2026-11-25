/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.OneSided
public import MathlibExt.CategoryTheory.Monoidal.Mod.RightTensorHom
public import MathlibExt.CategoryTheory.Monoidal.HomogeneousLocalization.AmbientTensorHom

/-!
# The two original outer actions on the bimodule mapping object

The source scalar acts by precomposition and the target scalar by
postcomposition. The precomposition map is transposed inside the actual
target module category, so its compatibility with the independent target
action is proved. The remaining relative mapping object will impose the
middle linearity equalizer on these original actions.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory MonoidalCategory MonoidalOpposite BraidedCategory MonObj
open CategoryTheory.HomogeneousLocalization
open scoped MonoidalCategory

namespace Bimod.InternalHom

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]
  {A B D : Mon C}

/-- The original right-tensor adjunction on every associative target module. -/
def ambientRightAdjunction (A : Mon C) (U : C) :
    Mod.AmbientTensor.rightFunctor A.X U ⊣ AmbientTensorHom.rightFunctor A.X U :=
  (AmbientTensorHom.adjunction A.X U).ofNatIsoLeft (Mod.AmbientTensor.rightToLeftNatIso A.X U).symm

/-- The complete module Hom function retains the original chosen tensor-right Hom function. -/
theorem ambientRightAdjunction_homEquiv (A : Mon C) (U : C) (M P : Mod C A.X)
    (f : Mod.AmbientTensor.rightModule A.X U M ⟶ P) :
    ((ambientRightAdjunction A U).homEquiv M P f).hom =
      (originalRightTensorAdjunction U).homEquiv M.X P.X f.hom := by
  rw [ambientRightAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply,
    AmbientTensorHom.adjunction_homEquiv]
  change (AmbientTensorHom.homEquiv A.X U M P
    ((Mod.AmbientTensor.rightToLeftIso A.X U M).inv ≫ f)).hom = _
  rw [AmbientTensorHom.homEquiv_hom, Mod.comp_hom', Mod.AmbientTensor.rightToLeftIso_inv,
    originalRightTensorAdjunction_homEquiv]


/-- The original target-module evaluation is the same complete tensor-right evaluation. -/
theorem ambientRightAdjunction_counit_hom (A : Mon C) (U : C) (P : Mod C A.X) :
    ((ambientRightAdjunction A U).counit.app P).hom =
      (originalRightTensorAdjunction U).counit.app P.X := by
  change (Mod.AmbientTensor.rightToLeftIso A.X U (AmbientTensorHom.cotensorModule A.X U P)).hom.hom ≫
    (AmbientTensorHom.evaluation A.X U P).hom = _
  rw [Mod.AmbientTensor.rightToLeftIso_hom, AmbientTensorHom.evaluation_hom,
    originalRightTensorAdjunction_counit]
  rfl

/-- The actual target action on the original internal-Hom carrier. -/
def leftModule (N : Bimod B D) (P : Bimod A D) : Mod C A.X :=
  AmbientTensorHom.cotensorModule A.X N.X (Bimod.toLeftModule P)

/-- The actual source action on that same original internal-Hom carrier. -/
def rightModule (N : Bimod B D) (P : Bimod A D) : RightModuleFree.Carrier B.X :=
  (Mod.RightLeftTensor.rightHomFunctor (Bimod.toLeftModule N)).obj P.X

/-- Precomposition by the original source action is an actual morphism of target modules. -/
def rightActionMap (N : Bimod B D) (P : Bimod A D) :
    Mod.AmbientTensor.rightModule A.X B.X (leftModule N P) ⟶ leftModule N P :=
  ((ambientRightAdjunction A N.X).homEquiv _ (Bimod.toLeftModule P))
    ((Mod.AmbientTensor.rightAssociateIso A.X B.X N.X (leftModule N P)).hom ≫
      Mod.AmbientTensor.rightMap A.X N.actLeft (𝟙 (leftModule N P)) ≫
        (ambientRightAdjunction A N.X).counit.app (Bimod.toLeftModule P))

/-- The full target-linear precomposition map is exactly the original source scalar action. -/
theorem rightActionMap_hom (N : Bimod B D) (P : Bimod A D) :
    (rightActionMap N P).hom = (rightModule N P).mod.smul := by
  rw [rightActionMap, ambientRightAdjunction_homEquiv]
  simp only [Mod.comp_hom', Mod.AmbientTensor.rightAssociateIso_hom, Mod.AmbientTensor.rightMap_hom,
    Mod.id_hom', id_tensorHom, ambientRightAdjunction_counit_hom]
  exact (Mod.RightLeftTensor.rightHomFunctor_smul (Bimod.toLeftModule N) P.X).symm

/-- The original ambient mapping object with both complete commuting outer actions. -/
def unbalanced (N : Bimod B D) (P : Bimod A D) : Bimod A B := by
  let L := leftModule N P
  let R := rightModule N P
  refine
    { X := (ihom N.X).obj P.X
      actLeft := L.mod.smul
      actRight := R.mod.smul
      one_actLeft := ModObj.one_smul_self A.X L.X
      left_assoc := ModObj.mul_smul_self A.X L.X
      actRight_one := ModObj.one_smul (M := mop B.X) R.X
      right_assoc := ModObj.mul_smul (M := mop B.X) R.X
      middle_assoc := ?_ }
  have h := (rightActionMap N P).isModHom.smul_hom
  rw [rightActionMap_hom] at h
  change ((α_ A.X L.X B.X).inv ≫ (L.mod.smul ▷ B.X)) ≫ R.mod.smul =
    (A.X ◁ R.mod.smul) ≫ L.mod.smul at h
  have h' := congrArg (fun k => (α_ A.X L.X B.X).hom ≫ k) h
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h'
  change (L.mod.smul ▷ B.X) ≫ R.mod.smul =
    (α_ A.X ((ihom N.X).obj P.X) B.X).hom ≫ (A.X ◁ R.mod.smul) ≫ L.mod.smul at h'
  exact h'

/-- The complete unbalanced bimodule Hom retains the literal original ambient carrier. -/
theorem unbalanced_X (N : Bimod B D) (P : Bimod A D) :
    (unbalanced N P).X = (ihom N.X).obj P.X := rfl

/-- Its complete target action is the original target-module cotensor action. -/
theorem unbalanced_actLeft (N : Bimod B D) (P : Bimod A D) :
    (unbalanced N P).actLeft = (leftModule N P).mod.smul := rfl

/-- Its complete source action is the original right-module Hom precomposition action. -/
theorem unbalanced_actRight (N : Bimod B D) (P : Bimod A D) :
    (unbalanced N P).actRight = (rightModule N P).mod.smul := rfl

end Bimod.InternalHom
