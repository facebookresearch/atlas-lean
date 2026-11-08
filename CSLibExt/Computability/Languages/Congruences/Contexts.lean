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

public import CSLibExt.Computability.Languages.Congruences.Quotients

/-!
# Two-sided language contexts

A fixed left and right word context changes only the accepting subset of an algebraic recognizer.
This simultaneously generalizes the left- and right-quotient constructions and exposes the exact
operation used in the definition of syntactic equivalence.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v

variable {Symbol : Type u} {Carrier : Type v}

/-- Insert a word between fixed left and right contexts before testing language membership. -/
def contextQuotient (L : Language Symbol) (left right : List Symbol) : Language Symbol :=
  {x | left ++ x ++ right ∈ L}

@[simp]
theorem mem_contextQuotient (L : Language Symbol) (left right x : List Symbol) :
    x ∈ contextQuotient L left right ↔ left ++ x ++ right ∈ L :=
  Iff.rfl

@[simp]
theorem contextQuotient_nil_nil (L : Language Symbol) :
    contextQuotient L [] [] = L := by
  ext x
  change ([] ++ x ++ [] ∈ L) ↔ x ∈ L
  simp

theorem contextQuotient_nil_left (L : Language Symbol) (right : List Symbol) :
    contextQuotient L [] right = rightQuotient L right := by
  ext x
  simp [contextQuotient, rightQuotient]

theorem contextQuotient_nil_right (L : Language Symbol) (left : List Symbol) :
    contextQuotient L left [] = L.leftQuotient left := by
  ext x
  change (left ++ x ++ [] ∈ L) ↔ left ++ x ∈ L
  simp

theorem contextQuotient_eq_left_right (L : Language Symbol) (left right : List Symbol) :
    contextQuotient L left right = rightQuotient (L.leftQuotient left) right := by
  ext x
  simp [contextQuotient, rightQuotient, List.append_assoc]

/-- Nested contexts compose by appending left contexts in application order and right contexts in
the reverse order. -/
theorem contextQuotient_contextQuotient (L : Language Symbol)
    (outerLeft outerRight innerLeft innerRight : List Symbol) :
    contextQuotient (contextQuotient L outerLeft outerRight) innerLeft innerRight =
      contextQuotient L (outerLeft ++ innerLeft) (innerRight ++ outerRight) := by
  ext x
  simp only [mem_contextQuotient]
  simp [List.append_assoc]

/-- The accepting subset obtained by surrounding an image with two fixed context images. -/
def contextAccept [Monoid Carrier] (morphism : FreeMonoid Symbol →* Carrier)
    (accept : Set Carrier) (left right : List Symbol) : Set Carrier :=
  {m | morphism (FreeMonoid.ofList left) * m * morphism (FreeMonoid.ofList right) ∈ accept}

/-- Every algebraic recognizer recognizes all fixed two-sided context quotients without changing
its carrier or morphism. -/
theorem Recognizes.contextQuotient [Monoid Carrier] {L : Language Symbol}
    {morphism : FreeMonoid Symbol →* Carrier} {accept : Set Carrier}
    (hrec : Recognizes L morphism accept) (left right : List Symbol) :
    Recognizes (contextQuotient L left right) morphism
      (contextAccept morphism accept left right) := by
  intro x
  change left ++ FreeMonoid.toList x ++ right ∈ L ↔
    morphism (FreeMonoid.ofList left) * morphism x *
      morphism (FreeMonoid.ofList right) ∈ accept
  change FreeMonoid.toList
      (FreeMonoid.ofList (left ++ FreeMonoid.toList x ++ right)) ∈ L ↔ _
  rw [hrec, FreeMonoid.ofList_append, FreeMonoid.ofList_append, map_mul, map_mul,
    FreeMonoid.ofList_toList]

/-- The syntactic monoid of a context quotient is a quotient of a submonoid of the original
syntactic monoid. -/
noncomputable def contextQuotientToSyntactic (L : Language Symbol) (left right : List Symbol) :
    MonoidHom.mrange (syntacticMorphism L) →* SyntacticMonoid (contextQuotient L left right) :=
  recognizerImageToSyntactic (syntacticMorphism L)
    (contextAccept (syntacticMorphism L) (syntacticAccept L) left right)
    ((recognizes_syntacticMorphism L).contextQuotient left right)

theorem contextQuotientToSyntactic_surjective (L : Language Symbol)
    (left right : List Symbol) :
    Function.Surjective (contextQuotientToSyntactic L left right) :=
  recognizerImageToSyntactic_surjective (syntacticMorphism L)
    (contextAccept (syntacticMorphism L) (syntacticAccept L) left right)
    ((recognizes_syntacticMorphism L).contextQuotient left right)

/-- Whenever both quotients are explicitly finite, a context quotient cannot have a larger
syntactic monoid than the image of the original syntactic morphism. -/
theorem card_syntacticMonoid_contextQuotient_le_mrange (L : Language Symbol)
    (left right : List Symbol)
    [Fintype (MonoidHom.mrange (syntacticMorphism L))]
    [Fintype (SyntacticMonoid (contextQuotient L left right))] :
    Fintype.card (SyntacticMonoid (contextQuotient L left right)) ≤
      Fintype.card (MonoidHom.mrange (syntacticMorphism L)) :=
  Fintype.card_le_of_surjective _ (contextQuotientToSyntactic_surjective L left right)

/-- Finite syntactic monoids are closed under inserting words into fixed contexts. -/
theorem finite_syntacticMonoid_contextQuotient (L : Language Symbol) (left right : List Symbol)
    [Finite (SyntacticMonoid L)] :
    Finite (SyntacticMonoid (contextQuotient L left right)) :=
  finite_syntacticMonoid_of_recognizer (syntacticMorphism L)
    (contextAccept (syntacticMorphism L) (syntacticAccept L) left right)
    ((recognizes_syntacticMorphism L).contextQuotient left right)

/-- Regular languages are closed under fixed two-sided contexts. -/
theorem IsRegular.contextQuotient {L : Language Symbol} (hL : L.IsRegular)
    (left right : List Symbol) : (contextQuotient L left right).IsRegular := by
  rw [Cslib.Language.isRegular_iff_finite_syntacticMonoid] at hL ⊢
  let _ : Finite (SyntacticMonoid L) := hL
  exact finite_syntacticMonoid_contextQuotient L left right

/-- Syntactic equivalence is equivalently agreement of the two words in every fixed context
quotient. -/
theorem syntacticRel_iff_mem_contextQuotient (L : Language Symbol)
    (x y : FreeMonoid Symbol) :
    syntacticRel L x y ↔
      ∀ left right,
        FreeMonoid.toList x ∈ contextQuotient L left right ↔
          FreeMonoid.toList y ∈ contextQuotient L left right := by
  constructor <;> intro h left right
  · simpa [mem_contextQuotient, FreeMonoid.toList_mul] using
      h (FreeMonoid.ofList left) (FreeMonoid.ofList right)
  · simpa only [mem_contextQuotient, FreeMonoid.toList_mul,
      FreeMonoid.toList_ofList] using
      h (FreeMonoid.toList left) (FreeMonoid.toList right)

end Cslib.Language
