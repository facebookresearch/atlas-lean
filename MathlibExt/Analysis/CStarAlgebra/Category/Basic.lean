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

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.CategoryTheory.ConcreteCategory.Basic

/-!
# The category of nonunital complex C-star algebras

Objects retain their actual carrier and its existing C-star dictionary.
Morphisms are the existing nonunital complex star-algebra homomorphisms.
There is no new norm, continuity assumption or algebra structure.
-/

@[expose] public section

universe u

open CategoryTheory

/-- **Category of nonunital C*-algebras.** Its objects are nonunital complex C*-algebras and its
morphisms are nonunital complex star-algebra homomorphisms. -/
structure NonUnitalCStarAlgCat : Type (u + 1) where
  /-- The underlying type of this nonunital complex C-star algebra. -/
  carrier : Type u
  [str : NonUnitalCStarAlgebra carrier]

attribute [instance] NonUnitalCStarAlgCat.str

namespace NonUnitalCStarAlgCat

instance instCoeSort : CoeSort NonUnitalCStarAlgCat.{u} (Type u) :=
  ⟨carrier⟩

/-- **C*-algebra as a categorical object.** A nonunital complex C*-algebra `A` gives an object with the
same carrier, norm, involution, and complex algebra structure. -/
abbrev of (A : Type u) [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgCat.{u} :=
  ⟨A⟩

instance category : Category.{u} NonUnitalCStarAlgCat.{u} where
  Hom A B := A →⋆ₙₐ[ℂ] B
  id A := NonUnitalStarAlgHom.id ℂ A
  comp f g := g.comp f
  id_comp := by
    intro A B f
    ext a
    rfl
  comp_id := by
    intro A B f
    ext a
    rfl
  assoc := by
    intro A B C D f g h
    ext a
    rfl

instance concreteCategory :
    ConcreteCategory NonUnitalCStarAlgCat.{u} (fun A B => A →⋆ₙₐ[ℂ] B) where
  hom f := f
  ofHom f := f
  hom_ofHom _f := rfl
  ofHom_hom _f := rfl
  id_apply _a := rfl
  comp_apply _f _g _a := rfl

/-- **Star homomorphism as a categorical morphism.** For nonunital complex C*-algebras `A,B`, a
nonunital complex star-algebra homomorphism `f : A → B` is a morphism between their associated
objects. -/
abbrev ofHom {A B : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) : of A ⟶ of B :=
  f

/-- **Star homomorphism of a categorical morphism.** A morphism between objects `A,B` in the category of
nonunital complex C*-algebras is its nonunital complex star-algebra homomorphism `A → B`. -/
abbrev hom {A B : NonUnitalCStarAlgCat.{u}} (f : A ⟶ B) : A →⋆ₙₐ[ℂ] B :=
  f

theorem id_apply (A : NonUnitalCStarAlgCat.{u}) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by
  rfl

theorem comp_apply {A B C : NonUnitalCStarAlgCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by
  rfl

@[ext]
theorem hom_ext {A B : NonUnitalCStarAlgCat.{u}} {f g : A ⟶ B}
    (h : ∀ a, f a = g a) : f = g :=
  NonUnitalStarAlgHom.ext h

end NonUnitalCStarAlgCat
