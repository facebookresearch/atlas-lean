/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.IntFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Opposite

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]

example (T : SymmetricTrace C) (S : SymmetricTrace D) (F : C ⥤ D) [F.Braided]
    (hF : T.Preserves S F) (X : IntConstruction T) :
    ((IntConstruction.map T S F hF).obj X).negative = F.obj X.negative := rfl

-- Functoriality covers arbitrary feedback composition and independent universes.
example (T : SymmetricTrace C) (S : SymmetricTrace D) (F : C ⥤ D) [F.Braided]
    (hF : T.Preserves S F) {X Y Z : IntConstruction T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (IntConstruction.map T S F hF).map (f ≫ g) =
      (IntConstruction.map T S F hF).map f ≫ (IntConstruction.map T S F hF).map g := by simp

example (T : SymmetricTrace C) {X Y : IntConstruction T} (f : X ⟶ Y) :
    IntConstruction.hom T ((IntConstruction.map T T (𝟭 C) T.preserves_id).map f) =
      IntConstruction.hom T f := by
  simp [IntConstruction.map, IntConstruction.mapCrossed]

-- A nonidentity functor reverses tensor order; its comparisons are braidings.
open MonoidalOpposite
local instance : SymmetricCategory Cᴹᵒᵖ where
  symmetry X Y := by
    apply Quiver.Hom.unmop_inj
    exact SymmetricCategory.symmetry (unmop Y) (unmop X)

example {A B U V : C} (f : A ⊗ V ⟶ B ⊗ U) :
    IntConstruction.mapCrossed (mopFunctor C) f =
      (β_ (mop A) (mop V)).hom ≫ f.mop ≫ (β_ (mop B) (mop U)).inv := rfl

#print axioms IntConstruction.mapCrossed_compose
#print axioms IntConstruction.map
