/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Commutative unital C-star algebras and their actual character-space functor

Objects retain the original commutative unital C-star algebra dictionary.
Morphisms are the existing unital complex star-algebra homomorphisms.
The contravariant functor uses the existing pointwise character space and
literal precomposition of a character with the original homomorphism.
No replacement norm, chosen compact space or desired category equivalence
is used. Zero algebras and the empty compact character space are allowed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite WeakDual

/-- **Category of commutative unital C*-algebras.** Objects are commutative unital complex C*-algebras
and morphisms are unital complex star-algebra homomorphisms. -/
structure CommCStarAlgCat : Type (u + 1) where
  /-- The original carrier of the algebra. -/
  carrier : Type u
  /-- Its existing commutative unital C-star algebra structure. -/
  [str : CommCStarAlgebra carrier]

attribute [instance] CommCStarAlgCat.str

namespace CommCStarAlgCat

instance instCoeSort : CoeSort CommCStarAlgCat.{u} (Type u) := ⟨carrier⟩

/-- **Commutative unital C*-algebra as an object.** A commutative unital complex C*-algebra `A`
determines a categorical object with its given carrier, norm, unit, and involution. -/
abbrev of (A : Type u) [CommCStarAlgebra A] : CommCStarAlgCat.{u} := ⟨A⟩

instance category : Category.{u} CommCStarAlgCat.{u} where
  Hom A B := A →⋆ₐ[ℂ] B
  id A := StarAlgHom.id ℂ A
  comp f g := g.comp f
  id_comp := by intro A B f; ext a; rfl
  comp_id := by intro A B f; ext a; rfl
  assoc := by intro A B C D f g h; ext a; rfl

instance concreteCategory : ConcreteCategory CommCStarAlgCat.{u} (fun A B => A →⋆ₐ[ℂ] B) where
  hom f := f
  ofHom f := f
  hom_ofHom _f := rfl
  ofHom_hom _f := rfl
  id_apply _a := rfl
  comp_apply _f _g _a := rfl

/-- **Homomorphism of a commutative C*-algebra morphism.** For commutative unital complex C*-algebras
`A,B`, a categorical morphism `A → B` is its unital complex star-algebra homomorphism. -/
abbrev hom {A B : CommCStarAlgCat.{u}} (f : A ⟶ B) : A →⋆ₐ[ℂ] B := f

@[ext]
theorem hom_ext {A B : CommCStarAlgCat.{u}} {f g : A ⟶ B} (h : ∀ a, f a = g a) : f = g :=
  StarAlgHom.ext h

/-- **Identity in the commutative C*-algebra category.** For a commutative unital complex C*-algebra `A`
and `a ∈ A`, the identity morphism sends `a` to itself. -/
theorem id_apply (A : CommCStarAlgCat.{u}) (a : A) : (𝟙 A : A ⟶ A) a = a := rfl

/-- **Composition in the commutative C*-algebra category.** For commutative unital complex C*-algebras
`A,B,C`, morphisms `f : A → B`, `g : B → C`, and `a ∈ A`, categorical composition evaluates to
`g(f(a))`. -/
theorem comp_apply {A B C : CommCStarAlgCat.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := rfl

/-- **Compact character space.** For a commutative unital complex C*-algebra `A`, its nonzero complex
characters form a compact Hausdorff space with the topology of pointwise convergence. -/
def characterSpaceObject (A : CommCStarAlgCat.{u}) : CompHaus.{u} :=
  CompHaus.of (characterSpace ℂ A)

/-- **Contravariant character-space map.** A unital complex star homomorphism `f : A → B` between
commutative unital complex C*-algebras induces the continuous map from the character space of `B` to
that of `A`, sending `χ` to `χ ∘ f`. -/
def characterSpaceMap {A B : CommCStarAlgCat.{u}} (f : A ⟶ B) :
    characterSpaceObject B ⟶ characterSpaceObject A :=
  CompHausLike.ofHom (fun _ => True) (CharacterSpace.compContinuousMap f)

/-- **Contravariant character-space functor.** The assignment of a commutative unital complex C*-algebra
to its compact Hausdorff character space and of a unital star homomorphism to character
precomposition is a contravariant functor. -/
def characterSpaceFunctor : CommCStarAlgCat.{u} ⥤ CompHaus.{u}ᵒᵖ where
  obj A := op (characterSpaceObject A)
  map f := (characterSpaceMap f).op
  map_id A := by
    apply Quiver.Hom.unop_inj
    ext φ
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    ext φ
    rfl

/-- **Carrier of the character-space functor.** For a commutative unital complex C*-algebra `A`, the
underlying set of its character-space functor image is precisely the space of nonzero complex
characters of `A`. -/
theorem characterSpaceFunctor_obj_carrier (A : CommCStarAlgCat.{u}) :
    ↥(unop (characterSpaceFunctor.obj A)) = characterSpace ℂ A := rfl

/-- **Evaluation of character precomposition.** For a unital star homomorphism `f : A → B` between
commutative unital complex C*-algebras, a character `χ` of `B`, and `a ∈ A`, the induced character
of `A` evaluates to `χ(f(a))`. -/
theorem characterSpaceFunctor_map_apply {A B : CommCStarAlgCat.{u}}
    (f : A ⟶ B) (φ : characterSpace ℂ B) (a : A) :
    let χ : characterSpace ℂ A := (characterSpaceFunctor.map f).unop φ;
    χ a = φ (f a) := rfl

end CommCStarAlgCat

end
