/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Morphisms

/-!
# Inverse images under free-monoid morphisms

Alphabet maps are a special case of substitutions that send each source letter to an arbitrary
target word.  Such substitutions are precisely monoid morphisms between free monoids.  Composing
a recognizer with a substitution recognizes the inverse-image language, proving closure of finite
syntactic monoids and regular languages under inverse morphisms.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v w

variable {Source : Type u} {Target : Type v}

/-- Inverse image of a language under a free-monoid morphism. -/
def wordMorphismPreimage (substitution : FreeMonoid Source →* FreeMonoid Target)
    (L : Language Target) : Language Source :=
  {x | FreeMonoid.toList (substitution (FreeMonoid.ofList x)) ∈ L}

@[simp]
theorem mem_wordMorphismPreimage_iff
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target)
    (x : List Source) :
    x ∈ wordMorphismPreimage substitution L ↔
      FreeMonoid.toList (substitution (FreeMonoid.ofList x)) ∈ L :=
  Iff.rfl

@[simp]
theorem wordMorphismPreimage_id (L : Language Source) :
    wordMorphismPreimage (MonoidHom.id (FreeMonoid Source)) L = L := by
  ext x
  change FreeMonoid.toList (FreeMonoid.ofList x) ∈ L ↔ x ∈ L
  rfl

/-- A free-monoid morphism acts on words as the homomorphism given by the images of the
letters. -/
theorem toList_wordMorphism_ofList (substitution : FreeMonoid Source →* FreeMonoid Target)
    (x : List Source) :
    FreeMonoid.toList (substitution (FreeMonoid.ofList x)) =
      (x.map fun a => FreeMonoid.toList (substitution (FreeMonoid.of a))).flatten := by
  induction x with
  | nil => simp
  | cons a x ih =>
      rw [FreeMonoid.ofList_cons, map_mul, FreeMonoid.toList_mul, ih]
      rfl

/-- The inverse image under a free-monoid morphism, as the preimage of the homomorphism given by
the images of the letters. -/
theorem wordMorphismPreimage_eq_flatten (substitution : FreeMonoid Source →* FreeMonoid Target)
    (L : Language Target) :
    wordMorphismPreimage substitution L =
      {x | (x.map fun a => FreeMonoid.toList (substitution (FreeMonoid.of a))).flatten ∈ L} := by
  ext x
  rw [mem_wordMorphismPreimage_iff, toList_wordMorphism_ofList]
  rfl

theorem wordMorphismPreimage_comp {Third : Type w}
    (outer : FreeMonoid Target →* FreeMonoid Third)
    (inner : FreeMonoid Source →* FreeMonoid Target) (L : Language Third) :
    wordMorphismPreimage inner (wordMorphismPreimage outer L) =
      wordMorphismPreimage (outer.comp inner) L := by
  ext x
  change FreeMonoid.toList
      (outer (FreeMonoid.ofList (FreeMonoid.toList (inner (FreeMonoid.ofList x))))) ∈ L ↔
    FreeMonoid.toList (outer (inner (FreeMonoid.ofList x))) ∈ L
  rw [FreeMonoid.ofList_toList]

/-- The recognizing morphism induced by a substitution. -/
def wordMorphismRecognizer (substitution : FreeMonoid Source →* FreeMonoid Target)
    (L : Language Target) : FreeMonoid Source →* SyntacticMonoid L :=
  (syntacticMorphism L).comp substitution

@[simp]
theorem wordMorphismRecognizer_apply
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target)
    (x : FreeMonoid Source) :
    wordMorphismRecognizer substitution L x = syntacticMorphism L (substitution x) :=
  rfl

theorem recognizes_wordMorphismRecognizer
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target) :
    Recognizes (wordMorphismPreimage substitution L) (wordMorphismRecognizer substitution L)
      (syntacticAccept L) := by
  intro x
  change FreeMonoid.toList (substitution x) ∈ L ↔
    syntacticMorphism L (substitution x) ∈ syntacticAccept L
  exact syntacticMorphism_mem_accept L (substitution x)

/-- Syntactic equivalence after substitution implies equivalence in the inverse-image
language. -/
theorem syntacticRel_wordMorphismPreimage_of_map
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target)
    {x y : FreeMonoid Source} (h : syntacticRel L (substitution x) (substitution y)) :
    syntacticRel (wordMorphismPreimage substitution L) x y := by
  intro p q
  change FreeMonoid.toList (substitution (p * x * q)) ∈ L ↔
    FreeMonoid.toList (substitution (p * y * q)) ∈ L
  simpa only [map_mul] using h (substitution p) (substitution q)

/-- The inverse-image syntactic monoid is a quotient of the image of the composed
recognizer. -/
noncomputable def wordMorphismPreimageToSyntactic
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target) :
    MonoidHom.mrange (wordMorphismRecognizer substitution L) →*
      SyntacticMonoid (wordMorphismPreimage substitution L) :=
  recognizerImageToSyntactic (wordMorphismRecognizer substitution L) (syntacticAccept L)
    (recognizes_wordMorphismRecognizer substitution L)

theorem wordMorphismPreimageToSyntactic_surjective
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target) :
    Function.Surjective (wordMorphismPreimageToSyntactic substitution L) :=
  recognizerImageToSyntactic_surjective (wordMorphismRecognizer substitution L)
    (syntacticAccept L) (recognizes_wordMorphismRecognizer substitution L)

/-- Finiteness of syntactic monoids is closed under arbitrary free-monoid inverse images. -/
theorem finite_syntacticMonoid_wordMorphismPreimage
    (substitution : FreeMonoid Source →* FreeMonoid Target) (L : Language Target)
    [Finite (SyntacticMonoid L)] :
    Finite (SyntacticMonoid (wordMorphismPreimage substitution L)) :=
  finite_syntacticMonoid_of_recognizer (wordMorphismRecognizer substitution L)
    (syntacticAccept L) (recognizes_wordMorphismRecognizer substitution L)

/-- Regular languages are closed under inverse free-monoid morphisms. -/
theorem IsRegular.wordMorphismPreimage {L : Language Target} (hL : L.IsRegular)
    (substitution : FreeMonoid Source →* FreeMonoid Target) :
    (wordMorphismPreimage substitution L).IsRegular := by
  rw [Cslib.Language.isRegular_iff_finite_syntacticMonoid] at hL ⊢
  let _ : Finite (SyntacticMonoid L) := hL
  exact finite_syntacticMonoid_wordMorphismPreimage substitution L

/-- Letterwise alphabet preimages agree with inverse images under the induced free-monoid
morphism. -/
theorem alphabetPreimage_eq_wordMorphismPreimage (f : Source → Target)
    (L : Language Target) :
    alphabetPreimage f L = wordMorphismPreimage (FreeMonoid.map f) L := by
  ext x
  rfl

end Cslib.Language
