/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.Hom

/-!
# The Segal subdivision carrier and endpoint functors

The existing category of Hom elements retains the reverse source and forward
target. This neutral module provides its carrier and endpoint API.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe v u
open CategoryTheory Opposite
namespace CategoryTheory

/-- The Segal subdivision category of `C`, reusing the category of elements
of the hom functor. -/
abbrev SegalSubdivision (C : Type u) [Category.{v} C] :=
  (Functor.hom C).Elements

namespace SegalSubdivision

variable (C : Type u) [Category.{v} C]

/-- Regard one morphism as an object of the Segal subdivision. -/
def mk {X Y : C} (f : X ⟶ Y) : SegalSubdivision C :=
  Functor.elementsMk (Functor.hom C) (Opposite.op X, Y) f

@[simp]
theorem mk_obj_fst {X Y : C} (f : X ⟶ Y) :
    (mk C f).obj.1 = Opposite.op X :=
  rfl

@[simp]
theorem mk_obj_snd {X Y : C} (f : X ⟶ Y) :
    (mk C f).obj.2 = Y :=
  rfl

@[simp]
theorem mk_val {X Y : C} (f : X ⟶ Y) :
    (mk C f).val = f :=
  rfl

/-- A morphism in the Segal subdivision is a factorization square whose
left edge points backwards. -/
def homMk {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (left : X' ⟶ X) (right : Y ⟶ Y')
    (w : left ≫ f ≫ right = g) : mk C f ⟶ mk C g :=
  Functor.Elements.homMk (left.op, right) w

@[simp]
theorem homMk_hom_fst {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (left : X' ⟶ X) (right : Y ⟶ Y')
    (w : left ≫ f ≫ right = g) :
    (homMk C left right w).hom.1 = left.op :=
  rfl

@[simp]
theorem homMk_hom_snd {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (left : X' ⟶ X) (right : Y ⟶ Y')
    (w : left ≫ f ≫ right = g) :
    (homMk C left right w).hom.2 = right :=
  rfl

/-- Every Segal-subdivision object is represented by its underlying arrow. -/
theorem mk_surjective (z : SegalSubdivision C) :
    ∃ (X Y : C) (f : X ⟶ Y), z = mk C f := by
  exact ⟨Opposite.unop z.obj.1, z.obj.2, z.val, rfl⟩

/-- The source endpoint, regarded contravariantly. -/
def source : SegalSubdivision C ⥤ Cᵒᵖ :=
  Functor.Elements.π (Functor.hom C) ⋙ Prod.fst Cᵒᵖ C

/-- The target endpoint. -/
def target : SegalSubdivision C ⥤ C :=
  Functor.Elements.π (Functor.hom C) ⋙ Prod.snd Cᵒᵖ C

@[simp]
theorem source_obj (f : SegalSubdivision C) :
    (source C).obj f = f.obj.1 :=
  rfl

@[simp]
theorem target_obj (f : SegalSubdivision C) :
    (target C).obj f = f.obj.2 :=
  rfl

@[simp]
theorem source_map {f g : SegalSubdivision C} (w : f ⟶ g) :
    (source C).map w = w.hom.1 :=
  rfl

@[simp]
theorem target_map {f g : SegalSubdivision C} (w : f ⟶ g) :
    (target C).map w = w.hom.2 :=
  rfl



end SegalSubdivision
end CategoryTheory
