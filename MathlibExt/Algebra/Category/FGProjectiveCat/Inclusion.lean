/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import MathlibExt.CategoryTheory.ExactCategory.Abelian

/-!
# Inclusion `FGProjectiveCat R ⥤ FGModuleCat R`

For an arbitrary ring `R`, every finitely generated projective `R`-module is finitely
generated. The predicate implication `isFGProjective ≤ isFG` induces the full-subcategory
inclusion `FGProjectiveCat R ⥤ FGModuleCat R` via `ObjectProperty.ιOfLE`.

The inclusion is fully faithful and additive, with object and morphism maps definitionally
the identity on underlying `ModuleCat` data. Composing with the forgetful functor to
`ModuleCat R` yields `FGProjectiveCat.toModuleCat` up to natural isomorphism. When `R` is
noetherian, it is exact for the split exact structure on the source and the abelian exact
structure on the target, which is used to define the Cartan map `K₀(R) → G₀(R)`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace ModuleCat

variable (R : Type u) [Ring R]

/-- `isFGProjective` implies `isFG`: every f.g. projective module is f.g. -/
lemma isFGProjective_le_isFG :
    isFGProjective.{v} (R := R) ≤ isFG.{v} (R := R) :=
  fun _ h => h.1

end ModuleCat

namespace FGProjectiveCat

variable (R : Type u) [Ring R]

/-- Full-subcategory inclusion `FGProjectiveCat R ⥤ FGModuleCat R` via `ιOfLE`. -/
def inclusion :
    FGProjectiveCat.{v} R ⥤ FGModuleCat.{v} R :=
  (ModuleCat.isFGProjective.{v} (R := R)).ιOfLE (ModuleCat.isFGProjective_le_isFG R)

/-- The inclusion is definitionally the identity on underlying `ModuleCat` objects. -/
@[simp]
lemma inclusion_obj_obj (X : FGProjectiveCat.{v} R) :
    ((inclusion R).obj X).obj = X.obj :=
  rfl

/-- The inclusion is definitionally the identity on underlying morphisms. -/
@[simp]
lemma inclusion_map_hom {X Y : FGProjectiveCat.{v} R} (f : X ⟶ Y) :
    ((inclusion R).map f).hom = f.hom :=
  rfl

/-- The inclusion composed with the forgetful functor is isomorphic to `toModuleCat`. -/
def inclusionCompForgetIso :
    inclusion (R := R) ⋙ forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ≅ toModuleCat (R := R) :=
  ObjectProperty.ιOfLECompιIso (ModuleCat.isFGProjective_le_isFG R)

/-- The inclusion `FGProjectiveCat R ⥤ FGModuleCat R` is full. -/
instance inclusion_full :
    (inclusion (R := R)).Full :=
  ObjectProperty.full_ιOfLE (ModuleCat.isFGProjective_le_isFG R)

/-- The inclusion `FGProjectiveCat R ⥤ FGModuleCat R` is faithful. -/
instance inclusion_faithful :
    (inclusion (R := R)).Faithful :=
  ObjectProperty.faithful_ιOfLE (ModuleCat.isFGProjective_le_isFG R)

/-- The inclusion `FGProjectiveCat R ⥤ FGModuleCat R` is additive. -/
instance inclusion_additive :
    (inclusion (R := R)).Additive where
  map_add := fun {_ _} _ _ => rfl

/-- When `R` is noetherian, the inclusion is exact for split vs abelian exact structures. -/
instance inclusion_isExact_of_noetherian [IsNoetherianRing R] :
    (inclusion (R := R)).IsExact :=
  ExactCategory.isExact_splitSource _

end FGProjectiveCat
