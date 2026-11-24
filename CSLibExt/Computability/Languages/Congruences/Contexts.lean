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

/-- **Context quotient.** Let $L$ be a language over an alphabet $A$ and let $u, v$ be words over
$A$. The context quotient of $L$ by $(u, v)$ is the language
$u^{-1} L v^{-1} = \{x \in A^* \mid uxv \in L\}$ of words that land in $L$ when placed between
$u$ and $v$. -/
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

/-- **Composing context quotients.** Let $L$ be a language over an alphabet $A$, and for words
$u, v$ over $A$ write $u^{-1} L v^{-1} = \{x \mid uxv \in L\}$. Then for all words
$u_1, v_1, u_2, v_2$ over $A$,
$u_2^{-1} (u_1^{-1} L v_1^{-1}) v_2^{-1} = (u_1 u_2)^{-1} L (v_2 v_1)^{-1}$. -/
theorem contextQuotient_contextQuotient (L : Language Symbol)
    (outerLeft outerRight innerLeft innerRight : List Symbol) :
    contextQuotient (contextQuotient L outerLeft outerRight) innerLeft innerRight =
      contextQuotient L (outerLeft ++ innerLeft) (innerRight ++ outerRight) := by
  ext x
  simp only [mem_contextQuotient]
  simp [List.append_assoc]

/-- **Accepting set for a context quotient.** Let $\varphi \colon A^* \to M$ be a monoid morphism
from the free monoid on an alphabet $A$ to a monoid $M$, let $P \subseteq M$, and let $u, v$ be
words over $A$. The accepting set for the context $(u, v)$ is
$\{m \in M \mid \varphi(u)\, m\, \varphi(v) \in P\}$. -/
def contextAccept [Monoid Carrier] (morphism : FreeMonoid Symbol →* Carrier)
    (accept : Set Carrier) (left right : List Symbol) : Set Carrier :=
  {m | morphism (FreeMonoid.ofList left) * m * morphism (FreeMonoid.ofList right) ∈ accept}

/-- **Recognizers recognize context quotients.** Let $\varphi \colon A^* \to M$ be a monoid
morphism from the free monoid on an alphabet $A$ to a monoid $M$ that recognizes a language $L$
over $A$ through $P \subseteq M$, that is, a word $x$ lies in $L$ exactly when $\varphi(x) \in P$.
Then for all words $u, v$ over $A$, $\varphi$ recognizes the context quotient
$\{x \mid uxv \in L\}$ through the set $\{m \in M \mid \varphi(u)\, m\, \varphi(v) \in P\}$. -/
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

/-- **The canonical map to the syntactic monoid of a context quotient.** Let $L$ be a language
over an alphabet $A$, let $u, v$ be words over $A$, and write
$u^{-1} L v^{-1} = \{x \mid uxv \in L\}$. Let $\eta$ be the syntactic morphism of $L$ and
$\eta'$ the syntactic morphism of $u^{-1} L v^{-1}$. This is the monoid morphism from the image
of $\eta$ to the syntactic monoid of $u^{-1} L v^{-1}$ that sends $\eta(x)$ to $\eta'(x)$ for
every word $x$ over $A$. -/
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

/-- **Size bound for the syntactic monoid of a context quotient.** Let $L$ be a language over an
alphabet $A$, let $u, v$ be words over $A$, and write $u^{-1} L v^{-1} = \{x \mid uxv \in L\}$
for the context quotient. If the image of the syntactic morphism of $L$ and the syntactic monoid
of $u^{-1} L v^{-1}$ are both finite, then the syntactic monoid of $u^{-1} L v^{-1}$ has at most
as many elements as the image of the syntactic morphism of $L$. -/
theorem card_syntacticMonoid_contextQuotient_le_mrange (L : Language Symbol)
    (left right : List Symbol)
    [Fintype (MonoidHom.mrange (syntacticMorphism L))]
    [Fintype (SyntacticMonoid (contextQuotient L left right))] :
    Fintype.card (SyntacticMonoid (contextQuotient L left right)) ≤
      Fintype.card (MonoidHom.mrange (syntacticMorphism L)) :=
  Fintype.card_le_of_surjective _ (contextQuotientToSyntactic_surjective L left right)

/-- **Context quotients preserve finiteness of the syntactic monoid.** Let $L$ be a language over
an alphabet $A$ whose syntactic monoid is finite. Then for all words $u, v$ over $A$, the
syntactic monoid of the context quotient $u^{-1} L v^{-1} = \{x \mid uxv \in L\}$ is finite. -/
theorem finite_syntacticMonoid_contextQuotient (L : Language Symbol) (left right : List Symbol)
    [Finite (SyntacticMonoid L)] :
    Finite (SyntacticMonoid (contextQuotient L left right)) :=
  finite_syntacticMonoid_of_recognizer (syntacticMorphism L)
    (contextAccept (syntacticMorphism L) (syntacticAccept L) left right)
    ((recognizes_syntacticMorphism L).contextQuotient left right)

/-- **Regular languages are closed under context quotients.** If $L$ is a regular language over
an alphabet $A$, then for all words $u, v$ over $A$, the context quotient
$u^{-1} L v^{-1} = \{x \mid uxv \in L\}$ is regular. -/
theorem IsRegular.contextQuotient {L : Language Symbol} (hL : L.IsRegular)
    (left right : List Symbol) : (contextQuotient L left right).IsRegular := by
  rw [Cslib.Language.isRegular_iff_finite_syntacticMonoid] at hL ⊢
  let _ : Finite (SyntacticMonoid L) := hL
  exact finite_syntacticMonoid_contextQuotient L left right

/-- **Syntactic equivalence via context quotients.** Let $L$ be a language over an alphabet $A$.
Two words $x, y$ over $A$ are syntactically equivalent for $L$ if and only if, for all words
$u, v$ over $A$, $x$ lies in the context quotient $u^{-1} L v^{-1} = \{w \mid uwv \in L\}$
exactly when $y$ does. -/
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
