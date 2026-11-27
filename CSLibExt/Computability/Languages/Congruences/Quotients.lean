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
# Algebraic recognition of language quotients

Left and right quotients by fixed words do not require a new recognizing monoid.  They only change
the accepting subset: on the left, pre-multiply an image by the fixed word; on the right,
post-multiply it.  We formulate both constructions for arbitrary algebraic recognizers and derive
finiteness and regularity closure for their syntactic monoids.

For left quotients there is also a direct automaton argument (`IsRegular.leftQuotient`): a DFA for
`L` started in the state it reaches on the prefix accepts `L.leftQuotient pre`.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v

variable {Symbol : Type u} {Carrier : Type v}

/-- **Right quotient of a language by a word.** For a language $L$ over an alphabet $\Sigma$ and a
word $w \in \Sigma^*$, the right quotient of $L$ by $w$ is the language
$\{x \in \Sigma^* : xw \in L\}$ of all words $x$ whose concatenation $xw$ with $w$ lies in $L$. -/
def rightQuotient (L : Language Symbol) (suffix : List Symbol) : Language Symbol :=
  {x | x ++ suffix ∈ L}

@[simp]
theorem mem_rightQuotient (L : Language Symbol) (suffix x : List Symbol) :
    x ∈ rightQuotient L suffix ↔ x ++ suffix ∈ L :=
  Iff.rfl

/-- **Accepting set for a left quotient.** Let $\varphi \colon A^* \to M$ be a monoid morphism
from the free monoid on an alphabet $A$ to a monoid $M$, let $P \subseteq M$, and let $u$ be a
word over $A$. The accepting set for the left quotient by $u$ is
$\{m \in M \mid \varphi(u)\, m \in P\}$. -/
def leftQuotientAccept [Monoid Carrier] (morphism : FreeMonoid Symbol →* Carrier)
    (accept : Set Carrier) (pre : List Symbol) : Set Carrier :=
  {m | morphism (FreeMonoid.ofList pre) * m ∈ accept}

/-- **Accepting set for a right quotient.** Let $\varphi \colon A^* \to M$ be a monoid morphism
from the free monoid on an alphabet $A$ to a monoid $M$, let $P \subseteq M$, and let $u$ be a
word over $A$. The accepting set for the right quotient by $u$ is
$\{m \in M \mid m\, \varphi(u) \in P\}$. -/
def rightQuotientAccept [Monoid Carrier] (morphism : FreeMonoid Symbol →* Carrier)
    (accept : Set Carrier) (suffix : List Symbol) : Set Carrier :=
  {m | m * morphism (FreeMonoid.ofList suffix) ∈ accept}

/-- **Recognizers recognize left quotients.** Let $\varphi \colon A^* \to M$ be a monoid morphism
from the free monoid on an alphabet $A$ to a monoid $M$ that recognizes a language $L$ over $A$
through $P \subseteq M$, that is, a word $x$ lies in $L$ exactly when $\varphi(x) \in P$. Then
for every word $u$ over $A$, $\varphi$ recognizes the left quotient $\{x \mid ux \in L\}$ through
the set $\{m \in M \mid \varphi(u)\, m \in P\}$. -/
theorem Recognizes.leftQuotient [Monoid Carrier] {L : Language Symbol}
    {morphism : FreeMonoid Symbol →* Carrier} {accept : Set Carrier}
    (hrec : Recognizes L morphism accept) (pre : List Symbol) :
    Recognizes (L.leftQuotient pre) morphism
      (leftQuotientAccept morphism accept pre) := by
  intro x
  rw [Language.mem_leftQuotient]
  change FreeMonoid.toList (FreeMonoid.ofList (pre ++ FreeMonoid.toList x)) ∈ L ↔
    morphism x ∈ leftQuotientAccept morphism accept pre
  rw [hrec]
  change morphism (FreeMonoid.ofList (pre ++ FreeMonoid.toList x)) ∈ accept ↔
    morphism (FreeMonoid.ofList pre) * morphism x ∈ accept
  rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_toList]

/-- **Recognizers recognize right quotients.** Let $\varphi \colon A^* \to M$ be a monoid
morphism from the free monoid on an alphabet $A$ to a monoid $M$ that recognizes a language $L$
over $A$ through $P \subseteq M$, that is, a word $x$ lies in $L$ exactly when $\varphi(x) \in P$.
Then for every word $u$ over $A$, $\varphi$ recognizes the right quotient $\{x \mid xu \in L\}$
through the set $\{m \in M \mid m\, \varphi(u) \in P\}$. -/
theorem Recognizes.rightQuotient [Monoid Carrier] {L : Language Symbol}
    {morphism : FreeMonoid Symbol →* Carrier} {accept : Set Carrier}
    (hrec : Recognizes L morphism accept) (suffix : List Symbol) :
    Recognizes (rightQuotient L suffix) morphism
      (rightQuotientAccept morphism accept suffix) := by
  intro x
  rw [mem_rightQuotient]
  change FreeMonoid.toList (FreeMonoid.ofList (FreeMonoid.toList x ++ suffix)) ∈ L ↔
    morphism x ∈ rightQuotientAccept morphism accept suffix
  rw [hrec]
  change morphism (FreeMonoid.ofList (FreeMonoid.toList x ++ suffix)) ∈ accept ↔
    morphism x * morphism (FreeMonoid.ofList suffix) ∈ accept
  rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_toList]

/-- **The canonical map to the syntactic monoid of a left quotient.** Let $L$ be a language over
an alphabet $A$, let $u$ be a word over $A$, and write $u^{-1} L = \{x \mid ux \in L\}$. Let
$\eta$ be the syntactic morphism of $L$ and $\eta'$ the syntactic morphism of $u^{-1} L$. This
is the monoid morphism from the image of $\eta$ to the syntactic monoid of $u^{-1} L$ that sends
$\eta(x)$ to $\eta'(x)$ for every word $x$ over $A$. -/
noncomputable def leftQuotientToSyntactic (L : Language Symbol) (pre : List Symbol) :
    MonoidHom.mrange (syntacticMorphism L) →* SyntacticMonoid (L.leftQuotient pre) :=
  recognizerImageToSyntactic (syntacticMorphism L)
    (leftQuotientAccept (syntacticMorphism L) (syntacticAccept L) pre)
    ((recognizes_syntacticMorphism L).leftQuotient pre)

theorem leftQuotientToSyntactic_surjective (L : Language Symbol) (pre : List Symbol) :
    Function.Surjective (leftQuotientToSyntactic L pre) :=
  recognizerImageToSyntactic_surjective (syntacticMorphism L)
    (leftQuotientAccept (syntacticMorphism L) (syntacticAccept L) pre)
    ((recognizes_syntacticMorphism L).leftQuotient pre)

/-- **The canonical map to the syntactic monoid of a right quotient.** Let $L$ be a language over
an alphabet $A$, let $u$ be a word over $A$, and write $L u^{-1} = \{x \mid xu \in L\}$. Let
$\eta$ be the syntactic morphism of $L$ and $\eta'$ the syntactic morphism of $L u^{-1}$. This
is the monoid morphism from the image of $\eta$ to the syntactic monoid of $L u^{-1}$ that sends
$\eta(x)$ to $\eta'(x)$ for every word $x$ over $A$. -/
noncomputable def rightQuotientToSyntactic (L : Language Symbol) (suffix : List Symbol) :
    MonoidHom.mrange (syntacticMorphism L) →* SyntacticMonoid (rightQuotient L suffix) :=
  recognizerImageToSyntactic (syntacticMorphism L)
    (rightQuotientAccept (syntacticMorphism L) (syntacticAccept L) suffix)
    ((recognizes_syntacticMorphism L).rightQuotient suffix)

theorem rightQuotientToSyntactic_surjective (L : Language Symbol) (suffix : List Symbol) :
    Function.Surjective (rightQuotientToSyntactic L suffix) :=
  recognizerImageToSyntactic_surjective (syntacticMorphism L)
    (rightQuotientAccept (syntacticMorphism L) (syntacticAccept L) suffix)
    ((recognizes_syntacticMorphism L).rightQuotient suffix)

/-- **Left quotients preserve finiteness of the syntactic monoid.** Let $L$ be a language over an
alphabet $A$ whose syntactic monoid is finite. Then for every word $u$ over $A$, the syntactic
monoid of the left quotient $u^{-1} L = \{x \mid ux \in L\}$ is finite. -/
theorem finite_syntacticMonoid_leftQuotient (L : Language Symbol) (pre : List Symbol)
    [Finite (SyntacticMonoid L)] : Finite (SyntacticMonoid (L.leftQuotient pre)) :=
  finite_syntacticMonoid_of_recognizer (syntacticMorphism L)
    (leftQuotientAccept (syntacticMorphism L) (syntacticAccept L) pre)
    ((recognizes_syntacticMorphism L).leftQuotient pre)

/-- **Right quotients preserve finiteness of the syntactic monoid.** Let $L$ be a language over
an alphabet $A$ whose syntactic monoid is finite. Then for every word $u$ over $A$, the syntactic
monoid of the right quotient $L u^{-1} = \{x \mid xu \in L\}$ is finite. -/
theorem finite_syntacticMonoid_rightQuotient (L : Language Symbol) (suffix : List Symbol)
    [Finite (SyntacticMonoid L)] : Finite (SyntacticMonoid (rightQuotient L suffix)) :=
  finite_syntacticMonoid_of_recognizer (syntacticMorphism L)
    (rightQuotientAccept (syntacticMorphism L) (syntacticAccept L) suffix)
    ((recognizes_syntacticMorphism L).rightQuotient suffix)

/-- **Regular languages are closed under right quotients by fixed words.** If $L$ is a regular
language over an alphabet $A$, then for every word $u$ over $A$, the right quotient
$L u^{-1} = \{x \mid xu \in L\}$ is regular. -/
theorem IsRegular.rightQuotient' {L : Language Symbol} (hL : L.IsRegular)
    (suffix : List Symbol) : (rightQuotient L suffix).IsRegular := by
  rw [Cslib.Language.isRegular_iff_finite_syntacticMonoid] at hL ⊢
  let _ : Finite (SyntacticMonoid L) := hL
  exact finite_syntacticMonoid_rightQuotient L suffix

/-- **Regular languages are closed under left quotients by fixed words.** If $L$ is a regular
language over an alphabet $A$, then for every word $u$ over $A$, the left quotient
$u^{-1} L = \{x \mid ux \in L\}$ is regular.

The proof starts a DFA for $L$ in the state it reaches on $u$. -/
theorem IsRegular.leftQuotient {L : Language Symbol} (hL : L.IsRegular) (pre : List Symbol) :
    (L.leftQuotient pre).IsRegular := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  refine ⟨σ, inferInstance, ⟨M.step, M.eval pre, M.accept⟩, ?_⟩
  ext w
  rw [DFA.mem_accepts, Language.mem_leftQuotient, DFA.mem_accepts, DFA.eval, DFA.eval,
    DFA.evalFrom_of_append]
  rfl

end Cslib.Language
