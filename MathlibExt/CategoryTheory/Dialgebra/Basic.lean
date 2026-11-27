/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Dialgebras of two functors

For `F G : C ⥤ D`, a dialgebra is an object `X` equipped with a morphism
`F.obj X ⟶ G.obj X`. Its morphisms are morphisms in `C` that commute with
these structure maps. This gives one category construction for systems of
natural connecting maps with different source and target degree functors.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- An object equipped with a map between its images under two functors. -/
structure Dialgebra (F G : C ⥤ D) where
  /-- The underlying object. -/
  A : C
  /-- The structure map. -/
  a : F.obj A ⟶ G.obj A

namespace Dialgebra

variable {F G : C ⥤ D}

/-- A morphism of dialgebras commutes with their structure maps. -/
structure Hom (X Y : Dialgebra F G) where
  /-- The underlying morphism. -/
  f : X.A ⟶ Y.A
  /-- Compatibility with the structure maps. -/
  h : F.map f ≫ Y.a = X.a ≫ G.map f

namespace Hom

/-- Dialgebra morphisms are determined by their underlying morphisms. -/
@[ext]
theorem ext {X Y : Dialgebra F G} {f g : Hom X Y} (h : f.f = g.f) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity dialgebra morphism. -/
def id (X : Dialgebra F G) : Hom X X where
  f := 𝟙 X.A
  h := by simp

/-- Composition of compatible structure maps. -/
def comp {X Y Z : Dialgebra F G} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  f := f.f ≫ g.f
  h := by
    rw [F.map_comp, G.map_comp, Category.assoc, g.h, ← Category.assoc, f.h,
      Category.assoc]

end Hom

instance : Category (Dialgebra F G) where
  Hom X Y := Hom X Y
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext
    simp [Hom.id, Hom.comp]
  comp_id f := by
    apply Hom.ext
    simp [Hom.id, Hom.comp]
  assoc f g h := by
    apply Hom.ext
    simp [Hom.comp, Category.assoc]

/-- The underlying morphism of an identity is an identity. -/
@[simp]
theorem id_f (X : Dialgebra F G) : (𝟙 X : X ⟶ X).f = 𝟙 X.A := rfl

/-- The underlying morphism of a composite is the composite. -/
@[simp, reassoc]
theorem comp_f {X Y Z : Dialgebra F G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).f = f.f ≫ g.f := rfl

/-- Forget the structure map of a dialgebra. -/
@[simps]
def forget (F G : C ⥤ D) : Dialgebra F G ⥤ C where
  obj X := X.A
  map f := f.f

instance : (forget F G).Faithful where
  map_injective := fun h => Hom.ext h

end Dialgebra

end CategoryTheory
