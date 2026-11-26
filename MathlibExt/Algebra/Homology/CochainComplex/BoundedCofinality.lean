/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.Bounded

/-!
# Component lifts and bounded object stabilization

A fully faithful zero-preserving functor F:A → B lifts a complex from
source objects X_i and isomorphisms e_i:F(X_i) ≅ K_i.
The source differential is the unique preimage of
e_j⁻¹∘d_K(i,j)∘e_i. These maps form a complex whose F-image is
isomorphic to K. Finite support of X gives a bounded source lift.

For additive fully faithful F between preadditive categories with zero
objects and binary biproducts in B, ordinary object stabilization
assumes every X∈B has a target complement Y with X⊞Y in the image.
It gives, for bounded K, a bounded target complement L and an image
representative of K⊞L. The strict condition uses a source complement
Y∈A and gives an image representative of K⊞F(L) with bounded L∈A.
The constructed complements have zero differentials and use the given
finite support windows.

References: C. Weibel, The K-book, IV.8.13 and V.Remark 2.2.1.
Source, target, morphism and complex-index universes are independent.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uA vA uB vB uI

namespace CategoryTheory.Functor

section ComplexLift

variable {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]
variable {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B]
variable (F : A ⥤ B) [F.PreservesZeroMorphisms] [F.Full] [F.Faithful]
variable {I : Type uI} {c : ComplexShape I}

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i.

The lifted A-complex has terms X_i and differential the preimage of e_j⁻¹∘d_K(i,j)∘e_i. -/
@[implicit_reducible]
def preimageHomologicalComplex (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) : HomologicalComplex A c where
  X := X
  d i j := F.preimage ((e i).hom ≫ K.d i j ≫ (e j).inv)
  shape i j hij := by
    apply F.map_injective
    rw [Functor.map_preimage, K.shape i j hij]
    simp only [zero_comp, comp_zero, Functor.map_zero]
  d_comp_d' i j k _ _ := by
    apply F.map_injective
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage, Functor.map_zero]
    calc
      ((e i).hom ≫ K.d i j ≫ (e j).inv) ≫ ((e j).hom ≫ K.d j k ≫ (e k).inv) =
          (e i).hom ≫ K.d i j ≫ ((e j).inv ≫ (e j).hom) ≫ K.d j k ≫ (e k).inv := by
            simp only [Category.assoc]
      _ = (e i).hom ≫ (K.d i j ≫ K.d j k) ≫ (e k).inv := by
        rw [Iso.inv_hom_id]
        simp only [Category.id_comp, Category.assoc]
      _ = 0 := by rw [K.d_comp_d]; simp

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i.

The degree-i term of the lifted complex is the chosen object X_i. -/
theorem preimageHomologicalComplex_X (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (i : I) :
    (F.preimageHomologicalComplex K X e).X i = X i := rfl

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i.

The lifted differential is the preimage under F of e_j⁻¹∘d_K(i,j)∘e_i. -/
theorem preimageHomologicalComplex_d (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (i j : I) :
    (F.preimageHomologicalComplex K X e).d i j =
      F.preimage ((e i).hom ≫ K.d i j ≫ (e j).inv) := rfl

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i.

Mapping the lifted differential by F returns the conjugated map e_j⁻¹∘d_K(i,j)∘e_i. -/
theorem map_preimageHomologicalComplex_d (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (i j : I) :
    F.map ((F.preimageHomologicalComplex K X e).d i j) =
      (e i).hom ≫ K.d i j ≫ (e j).inv :=
  F.map_preimage _

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i.

The component isomorphisms e_i assemble into the canonical complex isomorphism F(lift(K)) ≅ K. -/
def preimageHomologicalComplexIso (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) :
    (F.mapHomologicalComplex c).obj (F.preimageHomologicalComplex K X e) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents e (by
    intro i j _
    dsimp only [Functor.mapHomologicalComplex, preimageHomologicalComplex]
    rw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i.

The forward component of F(lift(K)) ≅ K in degree i is e_i. -/
theorem preimageHomologicalComplexIso_hom_f (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (i : I) :
    (F.preimageHomologicalComplexIso K X e).hom.f i = (e i).hom := rfl

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i.

The inverse component of F(lift(K)) ≅ K in degree i is e_i⁻¹. -/
theorem preimageHomologicalComplexIso_inv_f (K : HomologicalComplex B c) (X : I → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (i : I) :
    (F.preimageHomologicalComplexIso K X e).inv.f i = (e i).inv := rfl

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i. Take I=ℤ and assume X_j=0 outside a supplied interval [a,b].

The component lift is a bounded A-complex with support [a,b]. -/
@[implicit_reducible]
def boundedPreimageOfComponents (K : CochainComplex B ℤ) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) : CochainComplex.Bounded A :=
  CochainComplex.Bounded.of A (F.preimageHomologicalComplex K X e) a b hX

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i. Take I=ℤ and assume X_j=0 outside a supplied interval [a,b].

The degree-i term of the bounded lift is X_i. -/
theorem boundedPreimageOfComponents_X (K : CochainComplex B ℤ) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) (i : ℤ) :
    (F.boundedPreimageOfComponents K X e a b hX).obj.X i = X i := rfl

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i. Take I=ℤ and assume X_j=0 outside a supplied interval [a,b].

The bounded lift retains the differential preimage of e_j⁻¹∘d_K(i,j)∘e_i. -/
theorem boundedPreimageOfComponents_d (K : CochainComplex B ℤ) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) (i j : ℤ) :
    (F.boundedPreimageOfComponents K X e a b hX).obj.d i j =
      F.preimage ((e i).hom ≫ K.d i j ≫ (e j).inv) := rfl

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i. Take I=ℤ and assume X_j=0 outside a supplied interval [a,b].

The differential of its F-image is e_j⁻¹∘d_K(i,j)∘e_i. -/
theorem boundedPreimageOfComponents_map_d (K : CochainComplex B ℤ) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) (i j : ℤ) :
    ((F.mapCochainComplexBounded).obj
      (F.boundedPreimageOfComponents K X e a b hX)).obj.d i j =
        (e i).hom ≫ K.d i j ≫ (e j).inv :=
  F.map_preimageHomologicalComplex_d K X e i j

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i. Take I=ℤ and assume X_j=0 outside a supplied interval [a,b].

The bounded source lift has zero terms for j<a or b<j. -/
theorem boundedPreimageOfComponents_outside (K : CochainComplex B ℤ) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) (j : ℤ)
    (hj : j < a ∨ b < j) :
    IsZero ((F.boundedPreimageOfComponents K X e a b hX).obj.X j) := hX j hj

/-- Let A,B be categories with zero morphisms and F:A → B fully faithful
and preserving zero morphisms. For a B-complex K of any shape c on I,
choose X_i∈A and e_i:F(X_i) ≅ K_i. Take I=ℤ and assume X_j=0 outside a supplied interval [a,b].

The mapped bounded lift, as an underlying cochain complex, is canonically isomorphic to K. -/
def boundedPreimageOfComponentsRawIso (K : CochainComplex B ℤ) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ K.X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) :
    ((F.mapCochainComplexBounded).obj
      (F.boundedPreimageOfComponents K X e a b hX)).obj ≅ K :=
  F.preimageHomologicalComplexIso K X e

end ComplexLift

end CategoryTheory.Functor

namespace CochainComplex.BoundedCofinality

section Components

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B] [HasBinaryBiproducts B]
variable (F : A ⥤ B)

/-- Let A be a category, B have zero morphisms and binary biproducts,
and F:A → B be a functor. Fix a target object X.

Target-complement data consist of Y∈B, T∈A and an isomorphism F(T) ≅ X⊞Y. -/
structure TargetComponent (X : B) where
  /-- Let A be a category, B have zero morphisms and binary biproducts,
and F:A → B be a functor. Fix a target object X.

The target complement Y is an object of B in the stabilization F(T) ≅ X⊞Y. -/
  complement : B
  /-- Let A be a category, B have zero morphisms and binary biproducts,
and F:A → B be a functor. Fix a target object X.

The source representative T is an object of A whose image realizes X⊞Y. -/
  total : A
  /-- Let A be a category, B have zero morphisms and binary biproducts,
and F:A → B be a functor. Fix a target object X.

The component comparison is the isomorphism F(T) ≅ X⊞Y. -/
  comparison : F.obj total ≅ X ⊞ complement

/-- Let A be a category, B have zero morphisms and binary biproducts,
and F:A → B be a functor. Fix a target object X.

Source-complement data consist of Y,T∈A and an isomorphism F(T) ≅ X⊞F(Y). -/
structure SourceComponent (X : B) where
  /-- Let A be a category, B have zero morphisms and binary biproducts,
and F:A → B be a functor. Fix a target object X.

The complement Y is an object of A, whose image is the second target summand. -/
  complement : A
  /-- Let A be a category, B have zero morphisms and binary biproducts,
and F:A → B be a functor. Fix a target object X.

The source total T represents the stabilized target X⊞F(Y). -/
  total : A
  /-- Let A be a category, B have zero morphisms and binary biproducts,
and F:A → B be a functor. Fix a target object X.

The component comparison is the isomorphism F(T) ≅ X⊞F(Y). -/
  comparison : F.obj total ≅ X ⊞ F.obj complement

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈B with
X⊞Y in the essential image of F.

For each target X, the object-complement hypothesis supplies chosen target-complement data F(T) ≅ X⊞Y. -/
def chosenTargetComponent
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y)) (X : B) : TargetComponent F X :=
  Classical.choice (show Nonempty (TargetComponent F X) from by
    obtain ⟨Y, Z, ⟨e⟩⟩ := hcofinal X
    exact ⟨⟨Y, Z, e⟩⟩)

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F.

For each target X, the source-complement hypothesis supplies chosen strict data F(T) ≅ X⊞F(Y). -/
def chosenSourceComponent
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y)) (X : B) : SourceComponent F X :=
  Classical.choice (show Nonempty (SourceComponent F X) from by
    obtain ⟨Y, Z, ⟨e⟩⟩ := hcofinal X
    exact ⟨⟨Y, Z, e⟩⟩)

end Components

section ZeroDifferential

variable {A : Type uA} [Category.{vA} A] [HasZeroMorphisms A]

/-- Let A be a category with zero morphisms and X:ℤ → A any family.

The cochain complex with term X_i and every differential zero. -/
def zeroDifferentialComplex (X : ℤ → A) : CochainComplex A ℤ where
  X := X
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/-- Let A have zero morphisms and X:ℤ → A be a family.

The degree-i term of its zero-differential complex is X_i. -/
theorem zeroDifferentialComplex_X (X : ℤ → A) (i : ℤ) :
    (zeroDifferentialComplex X).X i = X i := rfl

/-- Let A have zero morphisms and X:ℤ → A be a family.

Every differential of its zero-differential complex is zero. -/
theorem zeroDifferentialComplex_d (X : ℤ → A) (i j : ℤ) :
    (zeroDifferentialComplex X).d i j = 0 := rfl

end ZeroDifferential

section Windows

variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasBinaryBiproducts B]
variable (F : A ⥤ B)

/-- Let A,B be preadditive with zero objects, B have binary biproducts, and F:A → B be additive fully faithful. For bounded B-complexes K,L, choose source components X_j, isomorphisms F(X_j) ≅ (K⊞L)^j and support [a,b] for X.

The bounded source lift has a canonical mapped comparison F(lift) ≅ K⊞L. -/
def boundedBiprodComparison [F.Additive] [F.Full] [F.Faithful]
    (K L : CochainComplex.Bounded B) (X : ℤ → A)
    (e : ∀ i, F.obj (X i) ≅ (K.obj ⊞ L.obj).X i) (a b : ℤ)
    (hX : ∀ j : ℤ, j < a ∨ b < j → IsZero (X j)) :
    (F.mapCochainComplexBounded).obj
      (F.boundedPreimageOfComponents (K.obj ⊞ L.obj) X e a b hX) ≅ K ⊞ L := by
  letI : PreservesBinaryBiproduct K L (CochainComplex.Bounded.ι B) :=
    preservesBinaryBiproduct_of_preservesBiproduct (CochainComplex.Bounded.ι B) K L
  exact (CochainComplex.Bounded.fullyFaithfulι B).preimageIso
    ((F.boundedPreimageOfComponentsRawIso (K.obj ⊞ L.obj) X e a b hX).trans
      ((CochainComplex.Bounded.ι B).mapBiprod K L).symm)

omit [Preadditive A] [HasZeroObject A] in
/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈B with
X⊞Y in the essential image of F. Assume B has a zero object and choose a window [a,b] for the
complement construction on a bounded B-complex K.

The degree-j target complement is the chosen complement of K^j inside [a,b] and the zero object of B outside. -/
@[implicit_reducible]
def ordinaryComplementX
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) : B :=
  if a ≤ j ∧ j ≤ b then
    (chosenTargetComponent F hcofinal (K.obj.X j)).complement else 0

omit [Preadditive A] [HasZeroObject B] in
/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈B with
X⊞Y in the essential image of F. Assume A has a zero object and choose [a,b] for a bounded B-complex K.

The source total in degree j is the chosen representative of K^j plus its target complement inside the window, and zero outside. -/
@[implicit_reducible]
def ordinarySourceX
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) : A :=
  if a ≤ j ∧ j ≤ b then
    (chosenTargetComponent F hcofinal (K.obj.X j)).total else 0

omit [Preadditive A] [HasZeroObject A] in
/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈B with
X⊞Y in the essential image of F. Assume B has a zero object and choose a window [a,b] for the
complement construction on a bounded B-complex K.

The ordinary target complement is the bounded zero-differential complex on these degreewise complement objects. -/
@[implicit_reducible]
def ordinaryComplement
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b : ℤ) : CochainComplex.Bounded B :=
  CochainComplex.Bounded.of B
    (zeroDifferentialComplex (ordinaryComplementX F hcofinal K a b)) a b (by
      intro j hj
      have hn : ¬(a ≤ j ∧ j ≤ b) := by simpa only [not_and_or, not_le] using hj
      simp only [zeroDifferentialComplex_X, ordinaryComplementX,
        ite_eq_right hn]
      exact isZero_zero B)

omit [Preadditive A] [HasZeroObject A] in
/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈B with
X⊞Y in the essential image of F. Assume B has a zero object and choose a window [a,b] for the
complement construction on a bounded B-complex K.

Every differential of the ordinary target complement is zero. -/
theorem ordinaryComplement_d
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b i j : ℤ) :
    (ordinaryComplement F hcofinal K a b).obj.d i j = 0 := rfl

omit [Preadditive A] [HasZeroObject B] in
/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈B with
X⊞Y in the essential image of F. Assume A has a zero object and choose [a,b] for a bounded B-complex K.

For j<a or b<j, the selected ordinary source-total object is zero. -/
theorem ordinarySourceX_outside
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) (hj : j < a ∨ b < j) :
    IsZero (ordinarySourceX F hcofinal K a b j) := by
  have hn : ¬(a ≤ j ∧ j ≤ b) := by simpa only [not_and_or, not_le] using hj
  simp only [ordinarySourceX, ite_eq_right hn]
  exact isZero_zero A

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈B with
X⊞Y in the essential image of F. Assume B has a zero object and choose a window [a,b] for the
complement construction on a bounded B-complex K. Assume A is preadditive with a zero object, F additive and K supported in [a,b].

The chosen source totals X_j have component isomorphisms F(X_j) ≅ (K⊞L)^j, where L is the ordinary zero-differential target complement. -/
def ordinaryComponentIso [F.Additive]
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (j : ℤ) :
    F.obj (ordinarySourceX F hcofinal K a b j) ≅
      (K.obj ⊞ (ordinaryComplement F hcofinal K a b).obj).X j := by
  by_cases hj : a ≤ j ∧ j ≤ b
  · simp only [ordinarySourceX, ite_eq_left hj]
    exact (chosenTargetComponent F hcofinal (K.obj.X j)).comparison.trans
      (by
        simpa only [ordinaryComplement, CochainComplex.Bounded.of_obj,
          zeroDifferentialComplex_X, ordinaryComplementX, ite_eq_left hj] using
          (HomologicalComplex.biprodXIso K.obj
            (ordinaryComplement F hcofinal K a b).obj j).symm)
  · simp only [ordinarySourceX, ite_eq_right hj]
    have hOutside : j < a ∨ b < j := by simpa only [not_and_or, not_le] using hj
    have hC : IsZero ((ordinaryComplement F hcofinal K a b).obj.X j) := by
      simp only [ordinaryComplement, CochainComplex.Bounded.of_obj,
        zeroDifferentialComplex_X, ordinaryComplementX, ite_eq_right hj]
      exact isZero_zero B
    have hT : IsZero ((K.obj ⊞ (ordinaryComplement F hcofinal K a b).obj).X j) :=
      ((biprod_isZero_iff _ _).mpr ⟨hK j hOutside, hC⟩).of_iso
        (HomologicalComplex.biprodXIso K.obj
          (ordinaryComplement F hcofinal K a b).obj j)
    exact F.mapZeroObject.trans hT.isoZero.symm

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈B with
X⊞Y in the essential image of F. Assume A and B are preadditive with zero objects, F is additive
fully faithful, and K is supported in [a,b].

The bounded source complex is lifted from the selected ordinary totals using the component comparisons with K⊞L. -/
@[implicit_reducible]
def ordinarySourceLift [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) : CochainComplex.Bounded A :=
  F.boundedPreimageOfComponents (K.obj ⊞ (ordinaryComplement F hcofinal K a b).obj)
    (ordinarySourceX F hcofinal K a b) (ordinaryComponentIso F hcofinal K a b hK) a b
    (ordinarySourceX_outside F hcofinal K a b)

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈B with
X⊞Y in the essential image of F. Assume A and B are preadditive with zero objects, F is additive
fully faithful, and K is supported in [a,b].

The canonical bounded isomorphism F(sourceLift) ≅ K⊞L uses the chosen target complement L. -/
def ordinaryComparison [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) :
    (F.mapCochainComplexBounded).obj (ordinarySourceLift F hcofinal K a b hK) ≅
      K ⊞ ordinaryComplement F hcofinal K a b :=
  boundedBiprodComparison F K (ordinaryComplement F hcofinal K a b)
    (ordinarySourceX F hcofinal K a b) (ordinaryComponentIso F hcofinal K a b hK) a b
    (ordinarySourceX_outside F hcofinal K a b)

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈B with
X⊞Y in the essential image of F. Assume A and B are preadditive with zero objects, F is additive
fully faithful, and K is supported in [a,b].

In degree i,j, the mapped source-lift differential is the conjugate of the differential of K⊞L by its component comparison isomorphisms. -/
theorem ordinarySourceLift_map_d [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (i j : ℤ) :
    ((F.mapCochainComplexBounded).obj (ordinarySourceLift F hcofinal K a b hK)).obj.d i j =
      (ordinaryComponentIso F hcofinal K a b hK i).hom ≫
        (K.obj ⊞ (ordinaryComplement F hcofinal K a b).obj).d i j ≫
          (ordinaryComponentIso F hcofinal K a b hK j).inv :=
  F.boundedPreimageOfComponents_map_d _ _ _ a b _ i j

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈B with
X⊞Y in the essential image of F. Assume A and B are preadditive with zero objects, F is additive
fully faithful, and K is supported in [a,b].

The ordinary source lift has zero terms outside [a,b]. -/
theorem ordinarySourceLift_outside [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (j : ℤ)
    (hj : j < a ∨ b < j) : IsZero ((ordinarySourceLift F hcofinal K a b hK).obj.X j) :=
  ordinarySourceX_outside F hcofinal K a b j hj

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈B with
X⊞Y in the essential image of F. Assume A,B preadditive with zero objects and F additive fully faithful.

Every bounded B-complex K has a bounded target complement L such that K⊞L belongs to the essential image of the bounded complex functor induced by F. -/
theorem ordinaryCofinal [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : B, F.essImage (X ⊞ Y)) :
    ∀ K : CochainComplex.Bounded B, ∃ L : CochainComplex.Bounded B,
      (F.mapCochainComplexBounded).essImage (K ⊞ L) := by
  intro K
  obtain ⟨a, b, hK⟩ := K.property
  exact ⟨ordinaryComplement F hcofinal K a b, ordinarySourceLift F hcofinal K a b hK,
    ⟨ordinaryComparison F hcofinal K a b hK⟩⟩

omit [Preadditive A] [HasZeroObject B] in
/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F. Assume A has a zero object and choose a window [a,b] for the
source-complement construction on a bounded B-complex K.

The strict source complement in degree j is the chosen Y_j∈A inside [a,b] and zero outside. -/
@[implicit_reducible]
def strictComplementX
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) : A :=
  if a ≤ j ∧ j ≤ b then
    (chosenSourceComponent F hcofinal (K.obj.X j)).complement else 0

omit [Preadditive A] [HasZeroObject B] in
/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F. Assume A has a zero object and choose a window [a,b] for the
source-complement construction on a bounded B-complex K.

The strict source total in degree j is the chosen representative T_j∈A inside [a,b] and zero outside. -/
@[implicit_reducible]
def strictSourceX
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) : A :=
  if a ≤ j ∧ j ≤ b then
    (chosenSourceComponent F hcofinal (K.obj.X j)).total else 0

omit [HasZeroObject B] in
/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F. Assume A has a zero object and choose a window [a,b] for the
source-complement construction on a bounded B-complex K. Assume A preadditive.

The strict complement L is the bounded zero-differential A-complex on the chosen source complement family. -/
@[implicit_reducible]
def strictComplement
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b : ℤ) : CochainComplex.Bounded A :=
  CochainComplex.Bounded.of A
    (zeroDifferentialComplex (strictComplementX F hcofinal K a b)) a b (by
      intro j hj
      have hn : ¬(a ≤ j ∧ j ≤ b) := by simpa only [not_and_or, not_le] using hj
      simp only [zeroDifferentialComplex_X, strictComplementX, ite_eq_right hn]
      exact isZero_zero A)

omit [HasZeroObject B] in
/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F. Assume A has a zero object and choose a window [a,b] for the
source-complement construction on a bounded B-complex K. Assume A preadditive.

Every differential of the strict source complement L is zero. -/
theorem strictComplement_d
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b i j : ℤ) :
    (strictComplement F hcofinal K a b).obj.d i j = 0 := rfl

omit [HasZeroObject B] in
/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F. Assume A has a zero object and choose a window [a,b] for the
source-complement construction on a bounded B-complex K. Assume A preadditive.

The strict complement L has zero terms for j<a or b<j. -/
theorem strictComplement_outside
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) (hj : j < a ∨ b < j) :
    IsZero ((strictComplement F hcofinal K a b).obj.X j) := by
  have hn : ¬(a ≤ j ∧ j ≤ b) := by simpa only [not_and_or, not_le] using hj
  simp only [strictComplement, CochainComplex.Bounded.of_obj,
    zeroDifferentialComplex_X, strictComplementX, ite_eq_right hn]
  exact isZero_zero A

omit [Preadditive A] [HasZeroObject B] in
/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F. Assume A has a zero object and choose a window [a,b] for the
source-complement construction on a bounded B-complex K.

The strict source-total object is zero in each degree outside [a,b]. -/
theorem strictSourceX_outside
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b j : ℤ) (hj : j < a ∨ b < j) :
    IsZero (strictSourceX F hcofinal K a b j) := by
  have hn : ¬(a ≤ j ∧ j ≤ b) := by simpa only [not_and_or, not_le] using hj
  simp only [strictSourceX, ite_eq_right hn]
  exact isZero_zero A

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F. Assume A has a zero object and choose a window [a,b] for the
source-complement construction on a bounded B-complex K. Assume A preadditive, F additive and K supported in [a,b].

The strict source totals have component isomorphisms F(T_j) ≅ (K⊞F(L))^j, where L is the zero-differential source complement. -/
def strictComponentIso [F.Additive]
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (j : ℤ) :
    F.obj (strictSourceX F hcofinal K a b j) ≅
      (K.obj ⊞ ((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b)).obj).X j := by
  by_cases hj : a ≤ j ∧ j ≤ b
  · simp only [strictSourceX, ite_eq_left hj]
    exact (chosenSourceComponent F hcofinal (K.obj.X j)).comparison.trans
      (by
        simpa only [Functor.mapCochainComplexBounded_obj_X, strictComplement,
          CochainComplex.Bounded.of_obj, zeroDifferentialComplex_X,
          strictComplementX, ite_eq_left hj] using
          (HomologicalComplex.biprodXIso K.obj
            ((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b)).obj j).symm)
  · simp only [strictSourceX, ite_eq_right hj]
    have hOutside : j < a ∨ b < j := by simpa only [not_and_or, not_le] using hj
    have hC : IsZero
        (((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b)).obj.X j) :=
      F.map_isZero (strictComplement_outside F hcofinal K a b j hOutside)
    have hT : IsZero
        ((K.obj ⊞ ((F.mapCochainComplexBounded).obj
          (strictComplement F hcofinal K a b)).obj).X j) :=
      ((biprod_isZero_iff _ _).mpr ⟨hK j hOutside, hC⟩).of_iso
        (HomologicalComplex.biprodXIso K.obj
          ((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b)).obj j)
    exact F.mapZeroObject.trans hT.isoZero.symm

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F. Assume A and B are preadditive with zero objects, F is additive
fully faithful, and K is supported in [a,b].

The bounded source complex is lifted from the strict total objects using their comparisons with K⊞F(L). -/
@[implicit_reducible]
def strictSourceLift [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) : CochainComplex.Bounded A :=
  F.boundedPreimageOfComponents
    (K.obj ⊞ ((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b)).obj)
    (strictSourceX F hcofinal K a b) (strictComponentIso F hcofinal K a b hK) a b
    (strictSourceX_outside F hcofinal K a b)

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F. Assume A and B are preadditive with zero objects, F is additive
fully faithful, and K is supported in [a,b].

The canonical bounded isomorphism F(sourceLift) ≅ K⊞F(L) retains the source complement L as an F-image summand. -/
def strictComparison [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) :
    (F.mapCochainComplexBounded).obj (strictSourceLift F hcofinal K a b hK) ≅
      K ⊞ (F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b) :=
  boundedBiprodComparison F K ((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b))
    (strictSourceX F hcofinal K a b) (strictComponentIso F hcofinal K a b hK) a b
    (strictSourceX_outside F hcofinal K a b)

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F. Assume A and B are preadditive with zero objects, F is additive
fully faithful, and K is supported in [a,b].

The mapped strict source differential is the conjugate of the differential of K⊞F(L) by the component comparison isomorphisms. -/
theorem strictSourceLift_map_d [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (i j : ℤ) :
    ((F.mapCochainComplexBounded).obj (strictSourceLift F hcofinal K a b hK)).obj.d i j =
      (strictComponentIso F hcofinal K a b hK i).hom ≫
        (K.obj ⊞ ((F.mapCochainComplexBounded).obj (strictComplement F hcofinal K a b)).obj).d i j ≫
          (strictComponentIso F hcofinal K a b hK j).inv :=
  F.boundedPreimageOfComponents_map_d _ _ _ a b _ i j

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F. Assume A and B are preadditive with zero objects, F is additive
fully faithful, and K is supported in [a,b].

The strict source lift has zero terms outside [a,b]. -/
theorem strictSourceLift_outside [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y))
    (K : CochainComplex.Bounded B) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j)) (j : ℤ)
    (hj : j < a ∨ b < j) : IsZero ((strictSourceLift F hcofinal K a b hK).obj.X j) :=
  strictSourceX_outside F hcofinal K a b j hj

/-- Let A be a category, B preadditive with binary biproducts, and
F:A → B a functor. Assume for every X∈B there is Y∈A with
X⊞F(Y) in the essential image of F. Assume A,B preadditive with zero objects and F additive fully faithful.

Every bounded B-complex K has a bounded source complement L∈Bounded(A) such that K⊞F(L) belongs to the essential image of the bounded functor induced by F. -/
theorem strictCofinal [F.Additive] [F.Full] [F.Faithful]
    (hcofinal : ∀ X : B, ∃ Y : A, F.essImage (X ⊞ F.obj Y)) :
    ∀ K : CochainComplex.Bounded B, ∃ L : CochainComplex.Bounded A,
      (F.mapCochainComplexBounded).essImage (K ⊞ (F.mapCochainComplexBounded).obj L) := by
  intro K
  obtain ⟨a, b, hK⟩ := K.property
  exact ⟨strictComplement F hcofinal K a b, strictSourceLift F hcofinal K a b hK,
    ⟨strictComparison F hcofinal K a b hK⟩⟩

end Windows

end CochainComplex.BoundedCofinality

end
