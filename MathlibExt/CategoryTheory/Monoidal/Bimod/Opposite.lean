/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.OneSided
public import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

/-!
# The original bimodules in the monoidal opposite

The original left and right actions are exchanged by the literal monoidal
opposite wrapper. The actual monoid-object equivalence supplies both scalar
objects. Every carrier, action and map is retained, and both complete
inverse functors are constructed.
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

/-- The actual opposite scalar from the existing monoid-object equivalence. -/
abbrev mopMon (A : Mon C) : Mon Cᴹᵒᵖ := (MonObj.mopEquiv C).functor.obj A

/-- The original bimodule carrier and actions, in their literal reversed tensor presentation. -/
def mopBimodule {A B : Mon C} (M : Bimod A B) : Bimod (mopMon B) (mopMon A) where
  X := mop M.X
  actLeft := M.actRight.mop
  actRight := M.actLeft.mop
  one_actLeft := congrArg Quiver.Hom.mop M.actRight_one
  left_assoc := congrArg Quiver.Hom.mop M.right_assoc
  actRight_one := congrArg Quiver.Hom.mop M.one_actLeft
  right_assoc := congrArg Quiver.Hom.mop M.left_assoc
  middle_assoc := by
    apply Quiver.Hom.unmop_inj
    change (A.X ◁ M.actRight) ≫ M.actLeft =
      (α_ A.X M.X B.X).inv ≫ (M.actLeft ▷ B.X) ≫ M.actRight
    rw [M.middle_assoc, Iso.inv_hom_id_assoc]

/-- The opposite object retains the literal original carrier. -/
theorem mopBimodule_X {A B : Mon C} (M : Bimod A B) : (mopBimodule M).X = mop M.X := rfl

/-- The complete opposite left action is the original right action. -/
theorem mopBimodule_actLeft {A B : Mon C} (M : Bimod A B) :
    (mopBimodule M).actLeft = M.actRight.mop := rfl

/-- The complete opposite right action is the original left action. -/
theorem mopBimodule_actRight {A B : Mon C} (M : Bimod A B) :
    (mopBimodule M).actRight = M.actLeft.mop := rfl

/-- Every original bimodule map retains its literal map and both action equations in the opposite. -/
def mopBimoduleMap {A B : Mon C} {M N : Bimod A B} (f : M ⟶ N) : mopBimodule M ⟶ mopBimodule N where
  hom := f.hom.mop
  left_act_hom := congrArg Quiver.Hom.mop f.right_act_hom
  right_act_hom := congrArg Quiver.Hom.mop f.left_act_hom

/-- The complete opposite arrow is the original wrapped carrier arrow. -/
theorem mopBimoduleMap_hom {A B : Mon C} {M N : Bimod A B} (f : M ⟶ N) :
    (mopBimoduleMap f).hom = f.hom.mop := rfl

/-- Unwrapping the opposite bimodule retains the original two outer actions. -/
def unmopBimodule (A B : Mon C) (M : Bimod (mopMon B) (mopMon A)) : Bimod A B where
  X := unmop M.X
  actLeft := M.actRight.unmop
  actRight := M.actLeft.unmop
  one_actLeft := congrArg Quiver.Hom.unmop M.actRight_one
  left_assoc := congrArg Quiver.Hom.unmop M.right_assoc
  actRight_one := congrArg Quiver.Hom.unmop M.one_actLeft
  right_assoc := congrArg Quiver.Hom.unmop M.left_assoc
  middle_assoc := by
    have h := congrArg Quiver.Hom.unmop M.middle_assoc
    change (A.X ◁ M.actLeft.unmop) ≫ M.actRight.unmop =
      (α_ A.X (unmop M.X) B.X).inv ≫ (M.actRight.unmop ▷ B.X) ≫ M.actLeft.unmop at h
    have h' := congrArg (fun t => (α_ A.X (unmop M.X) B.X).hom ≫ t) h
    simp only [Iso.hom_inv_id_assoc] at h'
    exact h'.symm

/-- Every original opposite bimodule arrow unwraps with both original action equations. -/
def unmopBimoduleMap (A B : Mon C) {M N : Bimod (mopMon B) (mopMon A)} (f : M ⟶ N) :
    unmopBimodule A B M ⟶ unmopBimodule A B N where
  hom := f.hom.unmop
  left_act_hom := congrArg Quiver.Hom.unmop f.right_act_hom
  right_act_hom := congrArg Quiver.Hom.unmop f.left_act_hom

/-- The original wrapping operation is functorial on every bimodule and every bimodule arrow. -/
def mopFunctor (A B : Mon C) : Bimod A B ⥤ Bimod (mopMon B) (mopMon A) where
  obj := mopBimodule
  map := mopBimoduleMap
  map_id _ := by apply Bimod.hom_ext; rfl
  map_comp _ _ := by apply Bimod.hom_ext; rfl

/-- The original unwrapping operation is the complete inverse functor. -/
def unmopFunctor (A B : Mon C) : Bimod (mopMon B) (mopMon A) ⥤ Bimod A B where
  obj := unmopBimodule A B
  map := unmopBimoduleMap A B
  map_id _ := by apply Bimod.hom_ext; rfl
  map_comp _ _ := by apply Bimod.hom_ext; rfl

/-- Both inverse presentations recover every entire original bimodule, including both actual actions. -/
theorem unmop_mopBimodule {A B : Mon C} (M : Bimod A B) : unmopBimodule A B (mopBimodule M) = M := by
  cases M
  rfl

/-- Both inverse presentations recover every entire original opposite bimodule. -/
theorem mop_unmopBimodule (A B : Mon C) (M : Bimod (mopMon B) (mopMon A)) :
    mopBimodule (unmopBimodule A B M) = M := by
  cases M
  rfl

/-- The complete original categories of bimodules are equivalent through the actual reversed tensor presentation. -/
def mopEquivalence (A B : Mon C) : Bimod A B ≌ Bimod (mopMon B) (mopMon A) where
  functor := mopFunctor A B
  inverse := unmopFunctor A B
  unitIso := NatIso.ofComponents (fun M => eqToIso (unmop_mopBimodule M).symm) (by
    intro M N f
    apply Bimod.hom_ext
    simp only [eqToIso.hom, Bimod.comp_hom']
    simp
    rfl)
  counitIso := NatIso.ofComponents (fun M => eqToIso (mop_unmopBimodule A B M)) (by
    intro M N f
    apply Bimod.hom_ext
    simp only [eqToIso.hom, Bimod.comp_hom']
    simp
    rfl)

end Bimod
