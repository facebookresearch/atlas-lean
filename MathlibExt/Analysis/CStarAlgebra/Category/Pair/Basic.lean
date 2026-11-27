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

public import MathlibExt.Analysis.CStarAlgebra.Category.Basic
public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient
public import Mathlib.CategoryTheory.NatTrans

/-!
# Actual C-star algebra and closed-ideal pairs

Objects are real algebras with real closed two-sided ideals. Morphisms are
actual ideal-preserving nonunital star homomorphisms. No relative group,
norm or excision conclusion is stored in this category.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

/-- **Category of C*-ideal pairs.** A C*-ideal pair `(A,J)` consists of a nonunital complex C*-algebra
`A` and a distinguished closed two-sided star ideal `J ⊆ A`. These pairs are the objects; a morphism
is a nonunital star homomorphism carrying the distinguished ideal into the distinguished ideal. -/
structure CStarPairCat : Type (u + 1) where
  /-- The actual ambient algebra, with its existing C-star dictionary. -/
  algebra : NonUnitalCStarAlgCat.{u}
  /-- The distinguished closed two-sided star ideal of the ambient algebra. -/
  ideal : ClosedStarIdeal algebra

namespace CStarPairCat

/-- **Morphism of C*-ideal pairs.** A C*-ideal pair `(A,J)` consists of a nonunital complex C*-algebra
`A` and a distinguished closed two-sided star ideal `J ⊆ A`. A morphism `(A,J) → (B,K)` is a
nonunital complex star homomorphism `f : A → B` satisfying `f(J) ⊆ K`. -/
@[ext]
structure Hom (P Q : CStarPairCat.{u}) where
  /-- The underlying nonunital star homomorphism of the actual algebras. -/
  hom : P.algebra →⋆ₙₐ[ℂ] Q.algebra
  ideal_mem : Set.MapsTo hom P.ideal Q.ideal

instance category : Category.{u} CStarPairCat.{u} where
  Hom := Hom
  id P :=
    { hom := NonUnitalStarAlgHom.id ℂ P.algebra
      ideal_mem := fun _ hx => hx }
  comp f g :=
    { hom := g.hom.comp f.hom
      ideal_mem := fun _ hx => g.ideal_mem (f.ideal_mem hx) }
  id_comp := by
    intro P Q f
    apply Hom.ext
    ext a
    rfl
  comp_id := by
    intro P Q f
    apply Hom.ext
    ext a
    rfl
  assoc := by
    intro P Q R T f g h
    apply Hom.ext
    ext a
    rfl

@[ext]
theorem hom_ext {P Q : CStarPairCat.{u}} {f g : P ⟶ Q}
    (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- **Ambient algebra functor for C*-ideal pairs.** A C*-ideal pair `(A,J)` consists of a nonunital
complex C*-algebra `A` and a distinguished closed two-sided star ideal `J ⊆ A`. The assignment
`(A,J) ↦ A`, retaining each ideal-preserving star homomorphism, is a functor to nonunital complex
C*-algebras. -/
def forget : CStarPairCat.{u} ⥤ NonUnitalCStarAlgCat.{u} where
  obj P := P.algebra
  map f := f.hom
  map_id _P := rfl
  map_comp _f _g := rfl

/-- **Whole-ideal pair functor.** A C*-ideal pair `(A,J)` consists of a nonunital complex C*-algebra `A`
and a distinguished closed two-sided star ideal `J ⊆ A`. Sending a nonunital complex C*-algebra `A`
to `(A,A)` and retaining its star homomorphisms defines the diagonal functor. -/
def diagonal : NonUnitalCStarAlgCat.{u} ⥤ CStarPairCat.{u} where
  obj A := ⟨A, ClosedStarIdeal.top A⟩
  map f :=
    { hom := f
      ideal_mem := fun _ _ => ClosedStarIdeal.mem_top _ }
  map_id A := by
    apply Hom.ext
    rfl
  map_comp f g := by
    apply Hom.ext
    rfl

/-- **Distinguished ideal as a C*-algebra.** A C*-ideal pair `(A,J)` consists of a nonunital complex
C*-algebra `A` and a distinguished closed two-sided star ideal `J ⊆ A`. The ideal `J`, with its
inherited norm and operations, is a nonunital complex C*-algebra. -/
def idealObject (P : CStarPairCat.{u}) : NonUnitalCStarAlgCat.{u} := by
  letI : NonUnitalCStarAlgebra P.ideal.carrier :=
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra P.ideal.carrier
      (h_closed := P.ideal.isClosed)
  exact NonUnitalCStarAlgCat.of P.ideal.carrier

/-- **Restriction of an ideal-preserving homomorphism.** A C*-ideal pair `(A,J)` consists of a nonunital
complex C*-algebra `A` and a distinguished closed two-sided star ideal `J ⊆ A`. A morphism `(A,J) →
(B,K)` restricts to a nonunital star homomorphism `J → K`. -/
def idealMap {P Q : CStarPairCat.{u}} (f : P ⟶ Q) :
    idealObject P ⟶ idealObject Q :=
  NonUnitalStarAlgHom.codRestrict
    (f.hom.comp (NonUnitalStarSubalgebraClass.subtype P.ideal.carrier))
    Q.ideal.carrier (fun x => f.ideal_mem x.property)

@[simp]
theorem idealMap_apply {P Q : CStarPairCat.{u}} (f : P ⟶ Q)
    (x : P.ideal.carrier) :
    ((idealMap f : P.ideal.carrier →⋆ₙₐ[ℂ] Q.ideal.carrier) x).val =
      f.hom (x : P.algebra) := by
  rfl

/-- **Distinguished-ideal functor.** A C*-ideal pair `(A,J)` consists of a nonunital complex C*-algebra
`A` and a distinguished closed two-sided star ideal `J ⊆ A`. Sending `(A,J)` to `J` and every
ideal-preserving homomorphism to its restriction defines a functor to nonunital complex C*-algebras. -/
def idealFunctor : CStarPairCat.{u} ⥤ NonUnitalCStarAlgCat.{u} where
  obj := idealObject
  map := idealMap
  map_id P := by
    apply NonUnitalCStarAlgCat.hom_ext
    intro x
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply NonUnitalCStarAlgCat.hom_ext
    intro x
    apply Subtype.ext
    rfl

/-- **Natural ideal inclusion for pairs.** A C*-ideal pair `(A,J)` consists of a nonunital complex
C*-algebra `A` and a distinguished closed two-sided star ideal `J ⊆ A`. The inclusions `J ↪ A` form
a natural transformation from the distinguished-ideal functor to the ambient-algebra functor. -/
def idealInclusion : NatTrans idealFunctor.{u} forget.{u} where
  app P := NonUnitalStarSubalgebraClass.subtype P.ideal.carrier
  naturality {P Q} f := by
    apply NonUnitalCStarAlgCat.hom_ext
    intro x
    rfl

/-- **Natural map to the whole-ideal pair.** A C*-ideal pair `(A,J)` consists of a nonunital complex
C*-algebra `A` and a distinguished closed two-sided star ideal `J ⊆ A`. The identity of `A` gives a
pair morphism `(A,J) → (A,A)`, natural in ideal-preserving homomorphisms. -/
def fullInclusion : NatTrans (𝟭 CStarPairCat.{u}) (forget ⋙ diagonal) where
  app P :=
    { hom := NonUnitalStarAlgHom.id ℂ P.algebra
      ideal_mem := fun _ _ => ClosedStarIdeal.mem_top _ }
  naturality {P Q} f := by
    apply Hom.ext
    ext a
    rfl

@[simp]
theorem fullInclusion_apply (P : CStarPairCat.{u}) (a : P.algebra) :
    Hom.hom (P := P) (Q := diagonal.obj (forget.obj P))
      (fullInclusion.app P) a = a := by
  rfl

end CStarPairCat
