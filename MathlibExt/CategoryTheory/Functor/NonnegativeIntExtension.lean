/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Data.Int.Order.Lemmas

/-!
# Extending a natural diagram to the integers by zero

For a functor indexed by `ℕ` in a category with a zero object, this file
constructs the functor indexed by `ℤ` which is zero in negative degrees and
agrees with the original functor in nonnegative degrees.
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

/-- The object family underlying extension of a natural diagram by zero to
negative integer indices. -/
noncomputable def nonnegativeIntObj (F : ℕ ⥤ C) (z : ℤ) : C :=
  if 0 ≤ z then F.obj z.toNat else 0

/-- At a nonnegative integer, `nonnegativeIntObj` is canonically the
corresponding object of the natural diagram. -/
noncomputable def nonnegativeIntObjIso (F : ℕ ⥤ C) (z : ℤ) (hz : 0 ≤ z) :
  nonnegativeIntObj F z ≅ F.obj z.toNat :=
  eqToIso (by rw [nonnegativeIntObj, ite_eq_left hz])

omit [HasZeroMorphisms C] in
/-- At a negative integer, `nonnegativeIntObj` is zero. -/
theorem isZero_nonnegativeIntObj_of_neg (F : ℕ ⥤ C) (z : ℤ) (hz : z < 0) :
    IsZero (nonnegativeIntObj F z) := by
  rw [nonnegativeIntObj, ite_eq_right (by omega)]
  exact isZero_zero C

/-- The map between zero-extended objects associated to an integer
inequality. -/
noncomputable def nonnegativeIntMap (F : ℕ ⥤ C) {a b : ℤ} (h : a ≤ b) :
    nonnegativeIntObj F a ⟶ nonnegativeIntObj F b :=
  if ha : 0 ≤ a then
    (nonnegativeIntObjIso F a ha).hom ≫
      F.map (homOfLE (Int.toNat_le_toNat h)) ≫
      (nonnegativeIntObjIso F b (ha.trans h)).inv
  else 0

/-- Coordinate formula for `nonnegativeIntMap` when its source index is
nonnegative. -/
@[reassoc (attr := simp)]
theorem nonnegativeIntObjIso_inv_comp_nonnegativeIntMap
    (F : ℕ ⥤ C) {a b : ℤ} (h : a ≤ b) (ha : 0 ≤ a) :
    (nonnegativeIntObjIso F a ha).inv ≫ nonnegativeIntMap F h =
      F.map (homOfLE (Int.toNat_le_toNat h)) ≫
        (nonnegativeIntObjIso F b (ha.trans h)).inv := by
  rw [nonnegativeIntMap, dite_eq_left ha, Iso.inv_hom_id_assoc]

/-- A map whose source integer is negative is zero. -/
theorem nonnegativeIntMap_eq_zero_of_neg
    (F : ℕ ⥤ C) {a b : ℤ} (h : a ≤ b) (ha : a < 0) :
    nonnegativeIntMap F h = 0 := by
  rw [nonnegativeIntMap, dite_eq_right (by omega)]

@[simp]
theorem nonnegativeIntMap_id (F : ℕ ⥤ C) (a : ℤ) :
    nonnegativeIntMap F (le_refl a) = 𝟙 _ := by
  by_cases ha : 0 ≤ a
  · rw [nonnegativeIntMap, dite_eq_left ha]
    simp
  · exact (isZero_nonnegativeIntObj_of_neg F a (by omega)).eq_of_src _ _

@[reassoc]
theorem nonnegativeIntMap_comp (F : ℕ ⥤ C)
    {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    nonnegativeIntMap F (hab.trans hbc) =
      nonnegativeIntMap F hab ≫ nonnegativeIntMap F hbc := by
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab
    have hc : 0 ≤ c := hb.trans hbc
    rw [nonnegativeIntMap, dite_eq_left ha,
      nonnegativeIntMap, dite_eq_left ha,
      nonnegativeIntMap, dite_eq_left hb]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hm : homOfLE (Int.toNat_le_toNat (hab.trans hbc)) =
        homOfLE (Int.toNat_le_toNat hab) ≫
          homOfLE (Int.toNat_le_toNat hbc) := by
      subsingleton
    rw [hm, F.map_comp]
    simp only [Category.assoc]
  · exact (isZero_nonnegativeIntObj_of_neg F a (by omega)).eq_of_src _ _

/-- Extend a natural diagram by zero to negative integer indices. -/
noncomputable def nonnegativeIntExtension (F : ℕ ⥤ C) : ℤ ⥤ C where
  obj z := nonnegativeIntObj F z
  map {_ _} f := nonnegativeIntMap F (leOfHom f)
  map_id a := nonnegativeIntMap_id F a
  map_comp {_ _ _} f g := nonnegativeIntMap_comp F (leOfHom f) (leOfHom g)

@[simp]
theorem nonnegativeIntExtension_obj (F : ℕ ⥤ C) (z : ℤ) :
    (nonnegativeIntExtension F).obj z = nonnegativeIntObj F z :=
  rfl

/-- The map of `nonnegativeIntExtension` associated to an integer
inequality. -/
theorem nonnegativeIntExtension_map (F : ℕ ⥤ C)
    {a b : ℤ} (h : a ≤ b) :
    (nonnegativeIntExtension F).map (homOfLE h) = nonnegativeIntMap F h :=
  rfl

/-- Coordinate formula for the zero-extended functor on a morphism with
nonnegative source. -/
@[reassoc (attr := simp)]
theorem nonnegativeIntExtension_objIso_inv_comp_map
    (F : ℕ ⥤ C) {a b : ℤ} (h : a ≤ b) (ha : 0 ≤ a) :
    (nonnegativeIntObjIso F a ha).inv ≫
        (nonnegativeIntExtension F).map (homOfLE h) =
      F.map (homOfLE (Int.toNat_le_toNat h)) ≫
        (nonnegativeIntObjIso F b (ha.trans h)).inv :=
  nonnegativeIntObjIso_inv_comp_nonnegativeIntMap F h ha

end CategoryTheory.Functor

end
