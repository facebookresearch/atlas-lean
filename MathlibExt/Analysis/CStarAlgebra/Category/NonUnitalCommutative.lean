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

public import MathlibExt.Analysis.CStarAlgebra.Category.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Opposites
public import MathlibExt.Analysis.Normed.Algebra.CharacterOnePointFunctor
public import MathlibExt.Topology.Category.LocallyCompactHausdorff.Partial

/-!
# The actual nonunital commutative category and pointed-character functor

Objects retain their original commutative nonunital C-star fields and maps
are the existing nonunital star homomorphisms. Their continuity is derived
from the existing C-star map bound, with no continuity premise. The original
character space has its existing pointwise locally compact topology; maps
are the actual infinity-preserving maps of its one-point compactification.
No equivalence, inverse object or chosen character model supplies DATA.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open CategoryTheory Opposite Topology WeakDual
open scoped CStarAlgebra OnePoint

universe u

/-- **Category of commutative nonunital C*-algebras.** Its objects are commutative nonunital complex
C*-algebras and its morphisms are nonunital complex star-algebra homomorphisms. -/
structure NonUnitalCommCStarAlgCat : Type (u + 1) where
  /-- The original algebra carrier. -/
  carrier : Type u
  /-- Its original commutative nonunital C-star algebra dictionary. -/
  [str : NonUnitalCommCStarAlgebra carrier]

attribute [instance] NonUnitalCommCStarAlgCat.str

namespace NonUnitalCommCStarAlgCat

instance instCoeSort : CoeSort NonUnitalCommCStarAlgCat.{u} (Type u) := ⟨carrier⟩

/-- **Commutative nonunital C*-algebra as an object.** A commutative nonunital complex C*-algebra `A`
gives an object with its given carrier, norm, involution, and complex algebra structure. -/
abbrev of (A : Type u) [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgCat.{u} := ⟨A⟩

/-- **Forgetting commutativity of a C*-algebra.** A commutative nonunital complex C*-algebra `A` gives
an object of the category of nonunital complex C*-algebras with the same carrier and norm. -/
def toNonUnitalCStarAlgCat (A : NonUnitalCommCStarAlgCat.{u}) : NonUnitalCStarAlgCat.{u} :=
  NonUnitalCStarAlgCat.of A

/-- The original commutative category uses the canonical general category's Hom, identity and composition. -/
instance category : Category.{u} NonUnitalCommCStarAlgCat.{u} where
  Hom A B := (NonUnitalCStarAlgCat.category).Hom (toNonUnitalCStarAlgCat A) (toNonUnitalCStarAlgCat B)
  id A := (NonUnitalCStarAlgCat.category).id (toNonUnitalCStarAlgCat A)
  comp f g := (NonUnitalCStarAlgCat.category).comp f g
  id_comp := by intro A B f; exact (NonUnitalCStarAlgCat.category).id_comp f
  comp_id := by intro A B f; exact (NonUnitalCStarAlgCat.category).comp_id f
  assoc := by intro A B C D f g h; exact (NonUnitalCStarAlgCat.category).assoc f g h

/-- **Forgetful functor for commutative C*-algebras.** Sending commutative nonunital complex C*-algebras
to nonunital complex C*-algebras and retaining their nonunital star homomorphisms defines a functor. -/
def forgetfulFunctor : NonUnitalCommCStarAlgCat.{u} ⥤ NonUnitalCStarAlgCat.{u} where
  obj := toNonUnitalCStarAlgCat
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Full faithfulness of forgetting commutativity.** The forgetful functor from commutative nonunital
complex C*-algebras to nonunital complex C*-algebras is fully faithful: it leaves each homomorphism
set unchanged. -/
def fullyFaithfulForgetful : forgetfulFunctor.FullyFaithful where
  preimage f := f
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- **Carrier under forgetting commutativity.** For a commutative nonunital complex C*-algebra `A`, the
underlying set remains `A` after passage to the nonunital C*-algebra category. -/
theorem toNonUnitalCStarAlgCat_carrier (A : NonUnitalCommCStarAlgCat.{u}) :
    ↥(toNonUnitalCStarAlgCat A) = A := rfl

instance concreteCategory :
    ConcreteCategory NonUnitalCommCStarAlgCat.{u} (fun A B => A →⋆ₙₐ[ℂ] B) where
  hom f := f
  ofHom f := f
  hom_ofHom _f := rfl
  ofHom_hom _f := rfl
  id_apply _a := rfl
  comp_apply _f _g _a := rfl

/-- **Values of the forgetful functor on morphisms.** For commutative nonunital complex C*-algebras
`A,B`, a nonunital star homomorphism `f : A → B`, and `a ∈ A`, the forgotten morphism evaluates to
`f(a)`. -/
theorem forgetfulFunctor_map_apply {A B : NonUnitalCommCStarAlgCat.{u}} (f : A ⟶ B) (a : A) :
    forgetfulFunctor.map f a = f a := rfl

/-- **Locally compact character space.** For a commutative nonunital complex C*-algebra `A`, its nonzero
complex characters form a locally compact Hausdorff space with the topology of pointwise
convergence. -/
def characterSpaceObject (A : NonUnitalCommCStarAlgCat.{u}) : LocallyCompactHausPartialCat.{u} := by
  let : LocallyCompactSpace (characterSpace ℂ A) := CharacterSpace.locallyCompactSpaceNonUnital
  exact LocallyCompactHausPartialCat.of (characterSpace ℂ A)

/-- **Partial character-space map.** For a nonunital star homomorphism `f : A → B` between commutative
nonunital complex C*-algebras, character precomposition extends to a continuous map from the
one-point compactification of the character space of `B` to that of `A`. It sends the point at
infinity to infinity and represents a morphism of locally compact Hausdorff spaces with partial
maps. -/
def characterSpaceMap {A B : NonUnitalCommCStarAlgCat.{u}} (f : A ⟶ B) :
    characterSpaceObject B ⟶ characterSpaceObject A := by
  let ρ : A →⋆ₙₐ[ℂ] B := ConcreteCategory.hom f
  exact LocallyCompactHausPartialCat.ofPointedMap
    (WeakDual.pointedCharacterMap ρ.toNonUnitalAlgHom (map_continuous ρ))

/-- **Contravariant nonunital character-space functor.** The character-space assignment for commutative
nonunital complex C*-algebras, with maps given by character precomposition on one-point
compactifications, defines a contravariant functor to locally compact Hausdorff spaces with partial
maps. -/
def characterSpaceFunctor : NonUnitalCommCStarAlgCat.{u} ⥤ LocallyCompactHausPartialCat.{u}ᵒᵖ where
  obj A := op (characterSpaceObject A)
  map f := (characterSpaceMap f).op
  map_id A := by
    apply Quiver.Hom.unop_inj
    apply Under.UnderMorphism.ext
    exact congrArg (fun f : C(OnePoint (characterSpace ℂ A), OnePoint (characterSpace ℂ A)) =>
      TopCat.ofHom f) WeakDual.onePointCharacterPrecomposition_id
  map_comp {A B C} f g := by
    apply Quiver.Hom.unop_inj
    apply Under.UnderMorphism.ext
    let ρ := ConcreteCategory.hom f
    let σ := ConcreteCategory.hom g
    exact congrArg (fun h : C(OnePoint (characterSpace ℂ C), OnePoint (characterSpace ℂ A)) =>
      TopCat.ofHom h)
      (WeakDual.onePointCharacterPrecomposition_comp ρ.toNonUnitalAlgHom σ.toNonUnitalAlgHom
        (map_continuous ρ) (map_continuous σ))

/-- **Carrier of a commutative nonunital C*-object.** Bundling a commutative nonunital complex
C*-algebra `A` as a categorical object leaves its underlying set equal to `A`. -/
@[simp]
theorem of_carrier (A : Type u) [NonUnitalCommCStarAlgebra A] : ↥(of A) = A := rfl

/-- **Carrier of the nonunital character-space object.** For a commutative nonunital complex C*-algebra
`A`, the underlying set of its locally compact character-space object is exactly its space of
nonzero complex characters. -/
@[simp]
theorem characterSpaceObject_carrier (A : NonUnitalCommCStarAlgCat.{u}) :
    ↥(characterSpaceObject A) = characterSpace ℂ A := rfl

/-- **One-point character precomposition.** For a nonunital star homomorphism `f : A → B` between
commutative nonunital complex C*-algebras, the extension of its partial character-space map to
one-point compactifications is precisely character precomposition, including the zero character
represented by infinity. -/
theorem characterSpaceMap_precomposition {A B : NonUnitalCommCStarAlgCat.{u}} (f : A ⟶ B) :
    LocallyCompactHausPartialCat.extension
      (X := characterSpaceObject B) (Y := characterSpaceObject A) (characterSpaceMap f) =
      WeakDual.onePointCharacterPrecomposition
        (ConcreteCategory.hom f : A →⋆ₙₐ[ℂ] B).toNonUnitalAlgHom
        (map_continuous (ConcreteCategory.hom f : A →⋆ₙₐ[ℂ] B)) := rfl

/-- **Evaluation of nonunital character precomposition.** For a nonunital star homomorphism `f : A → B`
between commutative nonunital complex C*-algebras, a character or the point at infinity `p` of `B`,
and `a ∈ A`, evaluating the induced character at `a` gives the evaluation of `p` at `f(a)`. Infinity
represents the zero character. -/
theorem characterSpaceMap_evaluation {A B : NonUnitalCommCStarAlgCat.{u}} (f : A ⟶ B)
    (p : OnePoint (characterSpace ℂ B)) (a : A) :
    (onePointCharacterSpaceHomeomorph (A := A)
      (LocallyCompactHausPartialCat.extension
        (X := characterSpaceObject B) (Y := characterSpaceObject A) (characterSpaceMap f) p) :
      WeakDual ℂ A) a =
      (onePointCharacterSpaceHomeomorph (A := B) p : WeakDual ℂ B) (ConcreteCategory.hom f a) := by
  rw [characterSpaceMap_precomposition]
  change (onePointCharacterSpaceHomeomorph (A := A)
    ((onePointCharacterSpaceHomeomorph (A := A)).symm
      (characterWithZeroPrecomposition
        (ConcreteCategory.hom f : A →⋆ₙₐ[ℂ] B).toNonUnitalAlgHom
        (map_continuous (ConcreteCategory.hom f : A →⋆ₙₐ[ℂ] B))
        (onePointCharacterSpaceHomeomorph (A := B) p))) : WeakDual ℂ A) a = _
  rw [Homeomorph.apply_symm_apply]
  exact characterWithZeroPrecomposition_apply
    (ConcreteCategory.hom f : A →⋆ₙₐ[ℂ] B).toNonUnitalAlgHom
    (map_continuous (ConcreteCategory.hom f : A →⋆ₙₐ[ℂ] B))
    (onePointCharacterSpaceHomeomorph (A := B) p) a

/-- **Character precomposition fixes infinity.** For a nonunital star homomorphism between commutative
nonunital complex C*-algebras, its map between the one-point compactified character spaces sends
infinity to infinity. -/
theorem characterSpaceMap_infty {A B : NonUnitalCommCStarAlgCat.{u}} (f : A ⟶ B) :
    LocallyCompactHausPartialCat.extension
      (X := characterSpaceObject B) (Y := characterSpaceObject A) (characterSpaceMap f) ∞ = ∞ :=
  LocallyCompactHausPartialCat.extension_infty
    (X := characterSpaceObject B) (Y := characterSpaceObject A) (characterSpaceMap f)

end NonUnitalCommCStarAlgCat

end
