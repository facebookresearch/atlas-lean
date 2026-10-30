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

public import CSLibExt.Computability.Languages.Congruences.Regularity

/-!
# Syntactic monoids under alphabet morphisms

The inverse image of a language under a map of alphabets is recognized by composing its
syntactic morphism with the induced free-monoid morphism.  This gives both a direct syntactic
relation theorem and closure of finite syntactic monoids, hence regular languages, under alphabet
preimages.  Alphabet equivalences yield sharper transport results.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v

variable {Source : Type u} {Target : Type v}

/-- The inverse image of a language under letterwise mapping. -/
def alphabetPreimage (f : Source → Target) (L : Language Target) : Language Source :=
  {x | x.map f ∈ L}

@[simp]
theorem mem_alphabetPreimage_iff (f : Source → Target) (L : Language Target)
    (x : List Source) : x ∈ alphabetPreimage f L ↔ x.map f ∈ L :=
  Iff.rfl

@[simp]
theorem alphabetPreimage_id (L : Language Source) : alphabetPreimage id L = L := by
  ext x
  change x.map id ∈ L ↔ x ∈ L
  rw [List.map_id]

theorem alphabetPreimage_comp {Third : Type*} (g : Target → Third) (f : Source → Target)
    (L : Language Third) :
    alphabetPreimage f (alphabetPreimage g L) = alphabetPreimage (g ∘ f) L := by
  ext x
  change (x.map f).map g ∈ L ↔ x.map (g ∘ f) ∈ L
  rw [List.map_map]

/-- Mapping words letterwise, then applying a monoid recognizer, gives the induced recognizer on
the source alphabet. -/
def alphabetPreimageMorphism (f : Source → Target) (L : Language Target) :
    FreeMonoid Source →* SyntacticMonoid L :=
  (syntacticMorphism L).comp (FreeMonoid.map f)

@[simp]
theorem alphabetPreimageMorphism_apply (f : Source → Target) (L : Language Target)
    (x : FreeMonoid Source) :
    alphabetPreimageMorphism f L x = syntacticMorphism L (FreeMonoid.map f x) :=
  rfl

/-- The pulled-back syntactic morphism recognizes the alphabet preimage. -/
theorem recognizes_alphabetPreimageMorphism (f : Source → Target) (L : Language Target) :
    Recognizes (alphabetPreimage f L) (alphabetPreimageMorphism f L) (syntacticAccept L) := by
  intro x
  change (FreeMonoid.toList x).map f ∈ L ↔
    syntacticMorphism L (FreeMonoid.map f x) ∈ syntacticAccept L
  exact syntacticMorphism_mem_accept L (FreeMonoid.map f x)

/-- Syntactic equivalence in the target language implies syntactic equivalence after mapping the
source words. -/
theorem syntacticRel_alphabetPreimage_of_map (f : Source → Target) (L : Language Target)
    {x y : FreeMonoid Source} (h : syntacticRel L (FreeMonoid.map f x) (FreeMonoid.map f y)) :
    syntacticRel (alphabetPreimage f L) x y := by
  intro u v
  change (FreeMonoid.toList (u * x * v)).map f ∈ L ↔
    (FreeMonoid.toList (u * y * v)).map f ∈ L
  simpa only [← FreeMonoid.toList_map, map_mul] using
    h (FreeMonoid.map f u) (FreeMonoid.map f v)

/-- The kernel of the pulled-back syntactic morphism refines the preimage language's syntactic
congruence. -/
theorem alphabetPreimageMorphism_ker_le (f : Source → Target) (L : Language Target) :
    Con.ker (alphabetPreimageMorphism f L) ≤ syntacticCon (alphabetPreimage f L) :=
  recognizer_ker_le_syntacticCon (recognizes_alphabetPreimageMorphism f L)

/-- The syntactic monoid of an alphabet preimage is a quotient of a submonoid of the original
syntactic monoid. -/
noncomputable def alphabetPreimageToSyntactic (f : Source → Target) (L : Language Target) :
    MonoidHom.mrange (alphabetPreimageMorphism f L) →*
      SyntacticMonoid (alphabetPreimage f L) :=
  recognizerImageToSyntactic (alphabetPreimageMorphism f L) (syntacticAccept L)
    (recognizes_alphabetPreimageMorphism f L)

theorem alphabetPreimageToSyntactic_surjective (f : Source → Target)
    (L : Language Target) : Function.Surjective (alphabetPreimageToSyntactic f L) :=
  recognizerImageToSyntactic_surjective (alphabetPreimageMorphism f L) (syntacticAccept L)
    (recognizes_alphabetPreimageMorphism f L)

/-- Finiteness of the target syntactic monoid passes to every alphabet preimage. -/
theorem finite_syntacticMonoid_alphabetPreimage (f : Source → Target) (L : Language Target)
    [Finite (SyntacticMonoid L)] : Finite (SyntacticMonoid (alphabetPreimage f L)) :=
  finite_syntacticMonoid_of_recognizer (alphabetPreimageMorphism f L) (syntacticAccept L)
    (recognizes_alphabetPreimageMorphism f L)

/-- Regular languages are closed under alphabet preimages. -/
theorem IsRegular.alphabetPreimage {L : Language Target} (hL : L.IsRegular)
    (f : Source → Target) : (alphabetPreimage f L).IsRegular := by
  rw [Cslib.Language.isRegular_iff_finite_syntacticMonoid] at hL ⊢
  let _ : Finite (SyntacticMonoid L) := hL
  exact finite_syntacticMonoid_alphabetPreimage f L

/-- A bijection of alphabets reflects regularity as well as preserving it. -/
theorem isRegular_alphabetPreimage_equiv_iff (e : Source ≃ Target) (L : Language Target) :
    (alphabetPreimage e L).IsRegular ↔ L.IsRegular := by
  constructor
  · intro h
    have hpre := Cslib.Language.IsRegular.alphabetPreimage h e.symm
    rw [alphabetPreimage_comp] at hpre
    have he : e ∘ e.symm = id := funext e.apply_symm_apply
    rw [he, alphabetPreimage_id] at hpre
    exact hpre
  · intro h
    exact Cslib.Language.IsRegular.alphabetPreimage h e

/-- Syntactic finiteness is invariant under renaming the alphabet by an equivalence. -/
theorem finite_syntacticMonoid_alphabetPreimage_equiv_iff (e : Source ≃ Target)
    (L : Language Target) :
    Finite (SyntacticMonoid (alphabetPreimage e L)) ↔ Finite (SyntacticMonoid L) := by
  rw [← isRegular_iff_finite_syntacticMonoid,
    ← isRegular_iff_finite_syntacticMonoid]
  exact isRegular_alphabetPreimage_equiv_iff e L

end Cslib.Language
