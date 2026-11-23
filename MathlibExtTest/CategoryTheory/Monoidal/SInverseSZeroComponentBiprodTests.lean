/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentBiprod

/-! # Tests for zero-component coordinatewise biproduct -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.SInverseSZeroComponentBiprod

open CategoryTheory.SInverseS

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check Pair.difference_pairBiprodObj
#check zeroComponentBiprodFunctor
#check zeroComponentBiprodFunctor_obj_obj
#check zeroComponentBiprodFunctor_map_hom
#check zeroComponentBiprodLeftPairingFunctor
#check zeroComponentBiprodRightPairingFunctor
#check zeroComponentBiprodLeftUnitFunctor
#check zeroComponentBiprodRightUnitFunctor
#check zeroComponentBiprodLeftPairingFunctor_obj
#check zeroComponentBiprodLeftPairingFunctor_map
#check zeroComponentBiprodRightPairingFunctor_obj
#check zeroComponentBiprodRightPairingFunctor_map
#check zeroComponentBiprodLeftUnitFunctor_obj_obj
#check zeroComponentBiprodRightUnitFunctor_obj_obj
#check zeroComponentBiprodLeftUnitFunctor_map_hom
#check zeroComponentBiprodRightUnitFunctor_map_hom
#check RawHom.biprodLeftUnitComponent
#check RawHom.biprodRightUnitComponent
#check RawHom.biprodLeftUnitStabilizerIso
#check RawHom.biprodRightUnitStabilizerIso
#check RawHom.biprodLeftUnit_naturality_rel
#check RawHom.biprodRightUnit_naturality_rel
#check zeroComponentBiprodLeftUnitIso
#check zeroComponentBiprodRightUnitIso
#check zeroComponentBiprodLeftUnitIso_app
#check zeroComponentBiprodRightUnitIso_app
#check zeroComponentBiprodLeftUnitIso_hom_app_hom
#check zeroComponentBiprodRightUnitIso_hom_app_hom
#check zeroComponentBiprodLeftUnitIso_hom_app_base_eq_right

example (X Y : Pair C) :
    (pairBiprodObj X Y).difference = X.difference + Y.difference :=
  Pair.difference_pairBiprodObj X Y

example (X Y : ZeroComponent (C := C)) :
    (pairBiprodObj X.obj Y.obj).difference = 0 := by
  rw [Pair.difference_pairBiprodObj, X.property, Y.property, add_zero]

example (X Y : ZeroComponent (C := C)) :
    (zeroComponentBiprodFunctor.obj (X, Y)).obj =
      pairBiprodObj X.obj Y.obj :=
  zeroComponentBiprodFunctor_obj_obj (X, Y)

example {X Y : ZeroComponent (C := C) × ZeroComponent (C := C)}
    (f : X ⟶ Y) :
    (zeroComponentBiprodFunctor.map f).hom =
      Hom.biprod f.1.hom f.2.hom :=
  zeroComponentBiprodFunctor_map_hom f

example (X : ZeroComponent (C := C)) :
    zeroComponentBiprodLeftPairingFunctor.obj X =
      (zeroComponentBaseObject (C := C), X) :=
  zeroComponentBiprodLeftPairingFunctor_obj X

example (X : ZeroComponent (C := C)) :
    zeroComponentBiprodRightPairingFunctor.obj X =
      (X, zeroComponentBaseObject (C := C)) :=
  zeroComponentBiprodRightPairingFunctor_obj X

example {X Y : ZeroComponent (C := C)} (f : X ⟶ Y) :
    (zeroComponentBiprodLeftUnitFunctor.map f).hom =
      Hom.biprod (𝟙 (zeroComponentBaseObject (C := C)).obj) f.hom :=
  zeroComponentBiprodLeftUnitFunctor_map_hom f

example {X Y : ZeroComponent (C := C)} (f : X ⟶ Y) :
    (zeroComponentBiprodRightUnitFunctor.map f).hom =
      Hom.biprod f.hom
        (𝟙 (zeroComponentBaseObject (C := C)).obj) :=
  zeroComponentBiprodRightUnitFunctor_map_hom f

example (X : Pair C) :
    (RawHom.biprodLeftUnitComponent X).stabilizer = (0 : C) :=
  rfl

example (X : Pair C) :
    (RawHom.biprodRightUnitComponent X).stabilizer = (0 : C) :=
  rfl

example (s : C) :
    (0 : C) ⊞ ((0 : C) ⊞ s) ≅ s ⊞ (0 : C) :=
  RawHom.biprodLeftUnitStabilizerIso s

example (s : C) :
    (0 : C) ⊞ (s ⊞ (0 : C)) ≅ s ⊞ (0 : C) :=
  RawHom.biprodRightUnitStabilizerIso s

example {X Y : Pair C} (f : RawHom X Y) :
    (((RawHom.id (zeroComponentBaseObject (C := C)).obj).biprod f).comp
        (RawHom.biprodLeftUnitComponent Y)).Rel
      ((RawHom.biprodLeftUnitComponent X).comp f) :=
  RawHom.biprodLeftUnit_naturality_rel f

example {X Y : Pair C} (f : RawHom X Y) :
    ((f.biprod
        (RawHom.id (zeroComponentBaseObject (C := C)).obj)).comp
        (RawHom.biprodRightUnitComponent Y)).Rel
      ((RawHom.biprodRightUnitComponent X).comp f) :=
  RawHom.biprodRightUnit_naturality_rel f

example {X Y : ZeroComponent (C := C)} (f : X ⟶ Y) :
    zeroComponentBiprodLeftUnitFunctor.map f ≫
        zeroComponentBiprodLeftUnitIso.hom.app Y =
      zeroComponentBiprodLeftUnitIso.hom.app X ≫ f :=
  zeroComponentBiprodLeftUnitIso.hom.naturality f

example {X Y : ZeroComponent (C := C)} (f : X ⟶ Y) :
    zeroComponentBiprodRightUnitFunctor.map f ≫
        zeroComponentBiprodRightUnitIso.hom.app Y =
      zeroComponentBiprodRightUnitIso.hom.app X ≫ f :=
  zeroComponentBiprodRightUnitIso.hom.naturality f

example (X : ZeroComponent (C := C)) :
    (zeroComponentBiprodLeftUnitIso.hom.app X).hom =
      Hom.mk (RawHom.biprodLeftUnitComponent X.obj) :=
  zeroComponentBiprodLeftUnitIso_hom_app_hom X

example (X : ZeroComponent (C := C)) :
    (zeroComponentBiprodRightUnitIso.hom.app X).hom =
      Hom.mk (RawHom.biprodRightUnitComponent X.obj) :=
  zeroComponentBiprodRightUnitIso_hom_app_hom X

example :
    zeroComponentBiprodLeftUnitIso.hom.app
        (zeroComponentBaseObject (C := C)) =
      zeroComponentBiprodRightUnitIso.hom.app
        (zeroComponentBaseObject (C := C)) :=
  zeroComponentBiprodLeftUnitIso_hom_app_base_eq_right

private abbrev ZeroCategory := SingleObj (ZMod 1)

private instance (X Y : ZeroCategory) : Subsingleton (X ⟶ Y) :=
  inferInstanceAs (Subsingleton (ZMod 1))

private instance : HasZeroObject ZeroCategory where
  zero :=
    ⟨SingleObj.star (ZMod 1),
      (IsZero.iff_id_eq_zero _).2 (Subsingleton.elim _ _)⟩

private instance : HasBinaryBiproducts ZeroCategory where
  has_binary_biproduct X Y := by
    apply hasBinaryBiproduct_of_total
      { pt := SingleObj.star (ZMod 1)
        fst := 0
        snd := 0
        inl := 0
        inr := 0
        inl_fst := Subsingleton.elim _ _
        inl_snd := Subsingleton.elim _ _
        inr_fst := Subsingleton.elim _ _
        inr_snd := Subsingleton.elim _ _ }
    exact Subsingleton.elim _ _

example :
    zeroComponentBiprodLeftUnitIso.hom.app
        (zeroComponentBaseObject (C := ZeroCategory)) =
      zeroComponentBiprodRightUnitIso.hom.app
        (zeroComponentBaseObject (C := ZeroCategory)) :=
  zeroComponentBiprodLeftUnitIso_hom_app_base_eq_right

section RaisedUniverses

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁]

example (X Y : ZeroComponent (C := C₁)) :
    (zeroComponentBiprodFunctor.obj (X, Y)).obj =
      pairBiprodObj X.obj Y.obj :=
  zeroComponentBiprodFunctor_obj_obj (X, Y)

example :
    zeroComponentBiprodLeftUnitIso.hom.app
        (zeroComponentBaseObject (C := C₁)) =
      zeroComponentBiprodRightUnitIso.hom.app
        (zeroComponentBaseObject (C := C₁)) :=
  zeroComponentBiprodLeftUnitIso_hom_app_base_eq_right

end RaisedUniverses

#print axioms Pair.difference_pairBiprodObj
#print axioms zeroComponentBiprodFunctor
#print axioms zeroComponentBiprodFunctor_obj_obj
#print axioms zeroComponentBiprodFunctor_map_hom
#print axioms zeroComponentBiprodLeftPairingFunctor
#print axioms zeroComponentBiprodRightPairingFunctor
#print axioms zeroComponentBiprodLeftUnitFunctor
#print axioms zeroComponentBiprodRightUnitFunctor
#print axioms zeroComponentBiprodLeftPairingFunctor_obj
#print axioms zeroComponentBiprodLeftPairingFunctor_map
#print axioms zeroComponentBiprodRightPairingFunctor_obj
#print axioms zeroComponentBiprodRightPairingFunctor_map
#print axioms zeroComponentBiprodLeftUnitFunctor_obj_obj
#print axioms zeroComponentBiprodRightUnitFunctor_obj_obj
#print axioms zeroComponentBiprodLeftUnitFunctor_map_hom
#print axioms zeroComponentBiprodRightUnitFunctor_map_hom
#print axioms RawHom.biprodLeftUnitComponent
#print axioms RawHom.biprodRightUnitComponent
#print axioms RawHom.biprodLeftUnitStabilizerIso
#print axioms RawHom.biprodRightUnitStabilizerIso
#print axioms RawHom.biprodLeftUnit_naturality_rel
#print axioms RawHom.biprodRightUnit_naturality_rel
#print axioms zeroComponentBiprodLeftUnitIso
#print axioms zeroComponentBiprodRightUnitIso
#print axioms zeroComponentBiprodLeftUnitIso_app
#print axioms zeroComponentBiprodRightUnitIso_app
#print axioms zeroComponentBiprodLeftUnitIso_hom_app_hom
#print axioms zeroComponentBiprodRightUnitIso_hom_app_hom
#print axioms zeroComponentBiprodLeftUnitIso_hom_app_base_eq_right

end MathlibExtTest.SInverseSZeroComponentBiprod

end
