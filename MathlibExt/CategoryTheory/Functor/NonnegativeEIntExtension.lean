/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Functor.NonnegativeIntExtension
public import Mathlib.Order.WithBotTop

/-!
# Completing a natural diagram at both extended-integer endpoints

Given a natural diagram, a target object, and a compatible family of maps to
that target, this file extends the diagram to `EInt`.  It is zero below degree
zero and at `⊥`, agrees with the natural diagram in nonnegative finite
degrees, and takes the value of the target object at `⊤`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C]

set_option backward.isDefEq.respectTransparency false in
/-- The map of a nonnegative integer extension in coordinates of the
underlying natural diagram. -/
@[reassoc (attr := simp)]
theorem nonnegativeIntExtension_map_comp_objIso_hom
    (F : ℕ ⥤ C) {a b : ℤ} (h : a ≤ b) (ha : 0 ≤ a) :
    (nonnegativeIntExtension F).map (homOfLE h) ≫
        (nonnegativeIntObjIso F b (ha.trans h)).hom =
      (nonnegativeIntObjIso F a ha).hom ≫
        F.map (homOfLE (Int.toNat_le_toNat h)) := by
  change nonnegativeIntMap F h ≫
      (nonnegativeIntObjIso F b (ha.trans h)).hom = _
  rw [nonnegativeIntMap, dite_eq_left ha]
  have hcancel :
      (F.map (homOfLE (Int.toNat_le_toNat h)) ≫
          (nonnegativeIntObjIso F b (ha.trans h)).inv) ≫
        (nonnegativeIntObjIso F b (ha.trans h)).hom =
      F.map (homOfLE (Int.toNat_le_toNat h)) := by
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    (((nonnegativeIntObjIso F a ha).hom ≫
        (F.map (homOfLE (Int.toNat_le_toNat h)) ≫
          (nonnegativeIntObjIso F b (ha.trans h)).inv)) ≫
        (nonnegativeIntObjIso F b (ha.trans h)).hom) =
      (nonnegativeIntObjIso F a ha).hom ≫
        ((F.map (homOfLE (Int.toNat_le_toNat h)) ≫
          (nonnegativeIntObjIso F b (ha.trans h)).inv) ≫
          (nonnegativeIntObjIso F b (ha.trans h)).hom) :=
        Category.assoc _ _ _
    _ = _ := by rw [hcancel]

/-- Extend a cocone map from a natural diagram to its zero extension at an
integer index. -/
noncomputable def nonnegativeIntToTopMap
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X) (z : ℤ) :
    (nonnegativeIntExtension F).obj z ⟶ X :=
  if hz : 0 ≤ z then
    (nonnegativeIntObjIso F z hz).hom ≫ ι.app z.toNat
  else 0

/-- Formula for the finite-to-top map at a nonnegative integer. -/
theorem nonnegativeIntToTopMap_of_nonneg
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X)
    (z : ℤ) (hz : 0 ≤ z) :
    nonnegativeIntToTopMap F X ι z =
      (nonnegativeIntObjIso F z hz).hom ≫ ι.app z.toNat := by
  rw [nonnegativeIntToTopMap, dite_eq_left hz]
  rfl

/-- The finite-to-top map at a negative integer is zero. -/
theorem nonnegativeIntToTopMap_of_neg
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X)
    (z : ℤ) (hz : z < 0) :
    nonnegativeIntToTopMap F X ι z = 0 := by
  rw [nonnegativeIntToTopMap, dite_eq_right (by omega)]

set_option backward.isDefEq.respectTransparency false in
/-- The finite-to-top maps are compatible with every map in the integer
zero extension. -/
@[reassoc (attr := simp)]
theorem nonnegativeIntExtension_map_comp_nonnegativeIntToTopMap
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X)
    {a b : ℤ} (h : a ≤ b) :
    (nonnegativeIntExtension F).map (homOfLE h) ≫
      nonnegativeIntToTopMap F X ι b =
      nonnegativeIntToTopMap F X ι a := by
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans h
    rw [nonnegativeIntToTopMap_of_nonneg F X ι a ha,
      nonnegativeIntToTopMap_of_nonneg F X ι b hb,
      nonnegativeIntExtension_map_comp_objIso_hom_assoc F h ha]
    have hn : F.map (homOfLE (Int.toNat_le_toNat h)) ≫ ι.app b.toNat =
        ι.app a.toNat := by
      have hn' := ι.naturality (homOfLE (Int.toNat_le_toNat h))
      have hc : ((Functor.const ℕ).obj X).map
          (homOfLE (Int.toNat_le_toNat h)) = 𝟙 X := rfl
      have hr : ι.app a.toNat ≫ ((Functor.const ℕ).obj X).map
          (homOfLE (Int.toNat_le_toNat h)) = ι.app a.toNat := by
        calc
          _ = ι.app a.toNat ≫ 𝟙 X :=
            congrArg (fun k ↦ ι.app a.toNat ≫ k) hc
          _ = ι.app a.toNat := Category.comp_id _
      exact hn'.trans hr
    simpa only [Category.assoc] using
      ((nonnegativeIntObjIso F a ha).hom ≫= hn)
  · exact (isZero_nonnegativeIntObj_of_neg F a (by omega)).eq_of_src _ _

/-- The object family underlying completion of a nonnegative integer diagram
at both extended-integer endpoints. -/
noncomputable def nonnegativeEIntObj (F : ℕ ⥤ C) (X : C) : EInt → C :=
  WithBotTop.rec 0 (nonnegativeIntExtension F).obj X

/-- The map associated to a morphism of extended-integer indices. -/
noncomputable def nonnegativeEIntMap
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X)
    {x y : EInt} (f : x ⟶ y) :
    nonnegativeEIntObj F X x ⟶ nonnegativeEIntObj F X y := by
    induction x using WithBotTop.rec with
    | bot =>
      induction y using WithBotTop.rec with
      | bot => exact 𝟙 _
      | coe _ => exact 0
      | top => exact 0
    | coe a =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b =>
          exact (nonnegativeIntExtension F).map
            (homOfLE (by simpa using leOfHom f))
      | top => exact nonnegativeIntToTopMap F X ι a
    | top =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe _ => exact 0
      | top => exact 𝟙 _

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem nonnegativeEIntMap_id
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X)
    (x : EInt) : nonnegativeEIntMap F X ι (𝟙 x) = 𝟙 _ := by
  induction x using WithBotTop.rec <;>
    simp [nonnegativeEIntMap, nonnegativeEIntObj]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem nonnegativeEIntMap_comp
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X)
    {x y z : EInt} (f : x ⟶ y) (g : y ⟶ z) :
    nonnegativeEIntMap F X ι (f ≫ g) =
      nonnegativeEIntMap F X ι f ≫ nonnegativeEIntMap F X ι g := by
    have hf := leOfHom f
    have hg := leOfHom g
    induction x using WithBotTop.rec <;>
      induction y using WithBotTop.rec <;>
      induction z using WithBotTop.rec <;>
      dsimp [nonnegativeEIntMap, nonnegativeEIntObj] at *
    all_goals try cat_disch
    case coe.coe.coe a b c =>
      have hab : a ≤ b := by simpa using hf
      have hbc : b ≤ c := by simpa using hg
      change nonnegativeIntMap F (hab.trans hbc) =
        nonnegativeIntMap F hab ≫ nonnegativeIntMap F hbc
      exact nonnegativeIntMap_comp F hab hbc

/-- Extend a natural diagram and a compatible target object to a diagram
indexed by the extended integers. -/
noncomputable def nonnegativeEIntExtension
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X) :
    EInt ⥤ C where
  obj := nonnegativeEIntObj F X
  map f := nonnegativeEIntMap F X ι f
  map_id x := nonnegativeEIntMap_id F X ι x
  map_comp f g := nonnegativeEIntMap_comp F X ι f g

@[simp]
theorem nonnegativeEIntExtension_obj_bot
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X) :
    (nonnegativeEIntExtension F X ι).obj ⊥ = 0 :=
  rfl

@[simp]
theorem nonnegativeEIntExtension_obj_coe
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X) (z : ℤ) :
    (nonnegativeEIntExtension F X ι).obj (z : EInt) =
      (nonnegativeIntExtension F).obj z :=
  rfl

@[simp]
theorem nonnegativeEIntExtension_obj_top
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X) :
    (nonnegativeEIntExtension F X ι).obj ⊤ = X :=
  rfl

/-- Formula for a map between finite integer indices. -/
theorem nonnegativeEIntExtension_map_coe
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X)
    {a b : ℤ} (h : a ≤ b) :
    (nonnegativeEIntExtension F X ι).map
        (homOfLE (show (a : EInt) ≤ b by simpa)) =
      (nonnegativeIntExtension F).map (homOfLE h) :=
  rfl

/-- Formula for the map from a finite integer index to `⊤`. -/
theorem nonnegativeEIntExtension_map_to_top
    (F : ℕ ⥤ C) (X : C) (ι : F ⟶ (Functor.const ℕ).obj X)
    (a : ℤ) :
    (nonnegativeEIntExtension F X ι).map
        (homOfLE (show (a : EInt) ≤ ⊤ by simp)) =
      nonnegativeIntToTopMap F X ι a :=
  rfl

end CategoryTheory.Functor

end
