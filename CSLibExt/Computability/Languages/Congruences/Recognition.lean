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

public import CSLibExt.Computability.Languages.Congruences.Syntactic

/-!
# Algebraic recognition of formal languages

A monoid morphism recognizes a language when membership is determined by the image of a word.
This file proves the universal property of the syntactic monoid: every recognizing morphism has a
kernel contained in the syntactic congruence, and consequently its kernel quotient maps onto the
syntactic monoid.  Equivalently, the syntactic monoid is a quotient of the transition information
carried by every algebraic recognizer.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v

variable {Symbol : Type u} {Carrier State : Type v}

/-- **Recognition of a language by a monoid morphism.** Let $L$ be a language over an alphabet
$\Sigma$, let $\varphi : \Sigma^* \to M$ be a monoid morphism from the free monoid on $\Sigma$
into a monoid $M$, and let $A \subseteq M$. Then $\varphi$ recognizes $L$ through $A$ when, for
every word $w \in \Sigma^*$, $w \in L$ if and only if $\varphi(w) \in A$. -/
def Recognizes [Monoid Carrier] (L : Language Symbol) (morphism : FreeMonoid Symbol →* Carrier)
    (accept : Set Carrier) : Prop :=
  ∀ x, FreeMonoid.toList x ∈ L ↔ morphism x ∈ accept

theorem Recognizes.mem_iff [Monoid Carrier] {L : Language Symbol}
    {morphism : FreeMonoid Symbol →* Carrier} {accept : Set Carrier}
    (h : Recognizes L morphism accept) (x : FreeMonoid Symbol) :
    FreeMonoid.toList x ∈ L ↔ morphism x ∈ accept :=
  h x

/-- **The syntactic morphism recognizes its language.** For every language $L$ over an alphabet
$\Sigma$, the syntactic morphism of $L$, from the free monoid $\Sigma^*$ to the syntactic monoid
of $L$, recognizes $L$ through the accepting subset of the syntactic monoid, namely the set of
syntactic classes of words in $L$. -/
theorem recognizes_syntacticMorphism (L : Language Symbol) :
    Recognizes L (syntacticMorphism L) (syntacticAccept L) :=
  syntacticMorphism_mem_accept L

/-- **Recognition pulls back along a factorization.** Let $L$ be a language over an
alphabet $\Sigma$ and let $\varphi : \Sigma^* \to C$ be a monoid morphism from the free monoid
$\Sigma^*$ that recognizes $L$ through a subset $A \subseteq C$. If $\varphi = f \circ \psi$ for
monoid morphisms $\psi : \Sigma^* \to T$ and $f : T \to C$, then $\psi$ recognizes $L$ through the
preimage $f^{-1}(A)$. -/
theorem Recognizes.comp [Monoid Carrier] {Target : Type*} [Monoid Target]
    {L : Language Symbol} {morphism : FreeMonoid Symbol →* Carrier} {accept : Set Carrier}
    (h : Recognizes L morphism accept) (factor : Target →* Carrier)
    (source : FreeMonoid Symbol →* Target) (hfactor : factor.comp source = morphism) :
    Recognizes L source (factor ⁻¹' accept) := by
  intro x
  rw [h x]
  change morphism x ∈ accept ↔ factor (source x) ∈ accept
  rw [← MonoidHom.comp_apply, hfactor]

/-- **Words with equal recognizer images are syntactically equivalent.** Let
$\varphi : \Sigma^* \to M$ be a monoid morphism from the free monoid on an alphabet $\Sigma$ into
a monoid $M$ that recognizes a language $L$ over $\Sigma$ through a set $A \subseteq M$. If two
words $x, y \in \Sigma^*$ satisfy $\varphi(x) = \varphi(y)$, then $x$ and $y$ are syntactically
equivalent for $L$: for all words $u, v \in \Sigma^*$, $uxv \in L$ if and only if $uyv \in L$. -/
theorem syntacticRel_of_recognizer_eq [Monoid Carrier] {L : Language Symbol}
    {morphism : FreeMonoid Symbol →* Carrier} {accept : Set Carrier}
    (hrec : Recognizes L morphism accept) {x y : FreeMonoid Symbol}
    (hxy : morphism x = morphism y) : syntacticRel L x y := by
  intro u v
  rw [hrec, hrec]
  simp only [map_mul]
  rw [hxy]

/-- **Recognizer kernels refine the syntactic congruence.** If a monoid morphism $\varphi$ from the
free monoid $\Sigma^*$ recognizes a language $L$ over $\Sigma$ through a subset $A$ of its
codomain, then the kernel congruence of $\varphi$ is contained in the syntactic congruence of $L$:
any words $x, y$ with $\varphi(x) = \varphi(y)$ are syntactically equivalent for $L$. -/
theorem recognizer_ker_le_syntacticCon [Monoid Carrier] {L : Language Symbol}
    {morphism : FreeMonoid Symbol →* Carrier} {accept : Set Carrier}
    (hrec : Recognizes L morphism accept) : Con.ker morphism ≤ syntacticCon L := by
  intro x y hxy
  exact syntacticRel_of_recognizer_eq hrec hxy

/-- **Canonical map from a recognizer's kernel quotient to the syntactic monoid.** Let $L$ be a
language over an alphabet $\Sigma$, let $\varphi : \Sigma^* \to M$ be a monoid morphism from the
free monoid on $\Sigma$ into a monoid $M$, and let $A \subseteq M$ be such that $\varphi$
recognizes $L$ through $A$. Since the kernel congruence of $\varphi$ (words $x, y$ with
$\varphi(x) = \varphi(y)$) is contained in the syntactic congruence of $L$, there is a monoid
morphism from the quotient of $\Sigma^*$ by the kernel of $\varphi$ to the syntactic monoid of
$L$ sending the class of each word $w$ to the syntactic class of $w$.

This is the algebraic minimality map before identifying the kernel quotient with the image of
the recognizer. -/
def recognizerQuotientToSyntactic [Monoid Carrier] {L : Language Symbol}
    (morphism : FreeMonoid Symbol →* Carrier) (accept : Set Carrier)
    (hrec : Recognizes L morphism accept) :
    (Con.ker morphism).Quotient →* SyntacticMonoid L :=
  Con.map (Con.ker morphism) (syntacticCon L) (recognizer_ker_le_syntacticCon hrec)

@[simp]
theorem recognizerQuotientToSyntactic_mk [Monoid Carrier] {L : Language Symbol}
    (morphism : FreeMonoid Symbol →* Carrier) (accept : Set Carrier)
    (hrec : Recognizes L morphism accept) (x : FreeMonoid Symbol) :
    recognizerQuotientToSyntactic morphism accept hrec ((Con.ker morphism).mk' x) =
      syntacticMorphism L x :=
  rfl

/-- **The kernel quotient of a recognizer maps onto the syntactic monoid.** If a monoid morphism
$\varphi$ from the free monoid $\Sigma^*$ recognizes a language $L$ over $\Sigma$ through a subset
$A$ of its codomain, then the canonical monoid morphism from the quotient of $\Sigma^*$ by the
kernel congruence of $\varphi$ to the syntactic monoid of $L$, which sends the class of a word
$x$ to its syntactic class, is surjective. -/
theorem recognizerQuotientToSyntactic_surjective [Monoid Carrier] {L : Language Symbol}
    (morphism : FreeMonoid Symbol →* Carrier) (accept : Set Carrier)
    (hrec : Recognizes L morphism accept) :
    Function.Surjective (recognizerQuotientToSyntactic morphism accept hrec) := by
  intro q
  obtain ⟨x, rfl⟩ := syntacticMorphism_surjective L q
  exact ⟨(Con.ker morphism).mk' x, recognizerQuotientToSyntactic_mk morphism accept hrec x⟩

/-- **Map from a recognizer's image to the syntactic monoid.** Let $\varphi : \Sigma^* \to M$ be a
monoid morphism from the free monoid $\Sigma^*$ that recognizes a language $L$ over $\Sigma$
through a subset $A \subseteq M$. This is the monoid morphism from the image $\varphi(\Sigma^*)$
to the syntactic monoid of $L$ that sends $\varphi(x)$ to the syntactic class of $x$ for every
word $x$. It is well defined because words with the same image under $\varphi$ are syntactically
equivalent for $L$. -/
noncomputable def recognizerImageToSyntactic [Monoid Carrier] {L : Language Symbol}
    (morphism : FreeMonoid Symbol →* Carrier) (accept : Set Carrier)
    (hrec : Recognizes L morphism accept) :
    MonoidHom.mrange morphism →* SyntacticMonoid L :=
  (recognizerQuotientToSyntactic morphism accept hrec).comp
    (Con.quotientKerEquivRange morphism).symm.toMonoidHom

@[simp]
theorem recognizerImageToSyntactic_image [Monoid Carrier] {L : Language Symbol}
    (morphism : FreeMonoid Symbol →* Carrier) (accept : Set Carrier)
    (hrec : Recognizes L morphism accept) (x : FreeMonoid Symbol) :
    recognizerImageToSyntactic morphism accept hrec ⟨morphism x, ⟨x, rfl⟩⟩ =
      syntacticMorphism L x := by
  change recognizerQuotientToSyntactic morphism accept hrec
    ((Con.quotientKerEquivRange morphism).symm ⟨morphism x, ⟨x, rfl⟩⟩) = _
  have hinv : (Con.quotientKerEquivRange morphism).symm ⟨morphism x, ⟨x, rfl⟩⟩ =
      (Con.ker morphism).mk' x := by
    apply (Con.quotientKerEquivRange morphism).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [hinv]
  exact recognizerQuotientToSyntactic_mk morphism accept hrec x

/-- **The image of a recognizer maps onto the syntactic monoid.** Let $\varphi : \Sigma^* \to M$ be
a monoid morphism from the free monoid $\Sigma^*$ that recognizes a language $L$ over $\Sigma$
through a subset $A \subseteq M$. Then the canonical monoid morphism from the image
$\varphi(\Sigma^*)$ to the syntactic monoid of $L$, which sends $\varphi(x)$ to the syntactic class
of $x$, is surjective. -/
theorem recognizerImageToSyntactic_surjective [Monoid Carrier] {L : Language Symbol}
    (morphism : FreeMonoid Symbol →* Carrier) (accept : Set Carrier)
    (hrec : Recognizes L morphism accept) :
    Function.Surjective (recognizerImageToSyntactic morphism accept hrec) := by
  intro q
  obtain ⟨x, rfl⟩ := syntacticMorphism_surjective L q
  exact ⟨⟨morphism x, ⟨x, rfl⟩⟩,
    recognizerImageToSyntactic_image morphism accept hrec x⟩

/-- **Finite recognizers give finite syntactic monoids.** If a monoid morphism from the free monoid
$\Sigma^*$ to a finite monoid $M$ recognizes a language $L$ over $\Sigma$ through some subset of
$M$, then the syntactic monoid of $L$ is finite. -/
theorem finite_syntacticMonoid_of_recognizer [Monoid Carrier] [Finite Carrier]
    {L : Language Symbol} (morphism : FreeMonoid Symbol →* Carrier) (accept : Set Carrier)
    (hrec : Recognizes L morphism accept) : Finite (SyntacticMonoid L) := by
  let _ : Finite (MonoidHom.mrange morphism) := Subtype.finite
  exact Finite.of_surjective (recognizerImageToSyntactic morphism accept hrec)
    (recognizerImageToSyntactic_surjective morphism accept hrec)

/-- **Recognition as an inverse image.** Let $L$ be a language over an alphabet $\Sigma$, let
$\varphi : \Sigma^* \to M$ be a monoid morphism from the free monoid on $\Sigma$ into a monoid
$M$, and let $A \subseteq M$. Then $\varphi$ recognizes $L$ through $A$ if and only if the set
of words of $\Sigma^*$ that belong to $L$ equals $\varphi^{-1}(A)$. -/
theorem recognizes_iff_preimage [Monoid Carrier] (L : Language Symbol)
    (morphism : FreeMonoid Symbol →* Carrier) (accept : Set Carrier) :
    Recognizes L morphism accept ↔
      {x | FreeMonoid.toList x ∈ L} = morphism ⁻¹' accept := by
  constructor
  · intro h
    ext x
    exact h x
  · intro h x
    exact Set.ext_iff.mp h x

/-- **Changing the accepting set off the image of a recognizer.** Let $\varphi : \Sigma^* \to M$ be
a monoid morphism from the free monoid $\Sigma^*$ that recognizes a language $L$ over $\Sigma$
through a subset $A_1 \subseteq M$. If $A_2 \subseteq M$ satisfies
$\varphi(x) \in A_1 \iff \varphi(x) \in A_2$ for every word $x$, then $\varphi$ also recognizes $L$
through $A_2$. -/
theorem Recognizes.congr_accept [Monoid Carrier] {L : Language Symbol}
    {morphism : FreeMonoid Symbol →* Carrier} {accept₁ accept₂ : Set Carrier}
    (hrec : Recognizes L morphism accept₁)
    (haccept : ∀ x, morphism x ∈ accept₁ ↔ morphism x ∈ accept₂) :
    Recognizes L morphism accept₂ := by
  intro x
  exact (hrec x).trans (haccept x)

/-! ## The canonical syntactic automaton -/

/-- **The syntactic DFA.** Let $L$ be a language over an alphabet $\Sigma$. The syntactic DFA of
$L$ has the syntactic monoid of $L$ as its set of states, the identity $1$ as start state, and
the syntactic classes of the words of $L$ as accepting states; from a state $q$, reading a
letter $a \in \Sigma$ leads to $q \cdot [a]$, where $[a]$ is the syntactic class of the
one-letter word $a$.

It is the direct automata-theoretic presentation of the canonical syntactic recognizer. -/
def syntacticDFA (L : Language Symbol) : DFA Symbol (SyntacticMonoid L) where
  step q a := q * syntacticMorphism L (FreeMonoid.of a)
  start := 1
  accept := syntacticAccept L

@[simp]
theorem syntacticDFA_start (L : Language Symbol) : (syntacticDFA L).start = 1 :=
  rfl

@[simp]
theorem syntacticDFA_step (L : Language Symbol) (q : SyntacticMonoid L) (a : Symbol) :
    (syntacticDFA L).step q a = q * syntacticMorphism L (FreeMonoid.of a) :=
  rfl

/-- **Runs of the syntactic DFA.** Let $L$ be a language over an alphabet $\Sigma$. For every
state $q$ of the syntactic DFA of $L$ (an element of the syntactic monoid of $L$) and every word
$x \in \Sigma^*$, the state reached from $q$ by reading $x$ is $q \cdot [x]$, where $[x]$ is the
image of $x$ under the syntactic morphism of $L$. -/
theorem syntacticDFA_evalFrom (L : Language Symbol) (q : SyntacticMonoid L)
    (x : List Symbol) :
    (syntacticDFA L).evalFrom q x = q * syntacticMorphism L (FreeMonoid.ofList x) := by
  induction x generalizing q with
  | nil => simp [syntacticDFA]
  | cons a x ih =>
    rw [DFA.evalFrom_cons, syntacticDFA_step, ih]
    simp only [FreeMonoid.ofList_cons, map_mul, mul_assoc]

@[simp]
theorem syntacticDFA_eval (L : Language Symbol) (x : List Symbol) :
    (syntacticDFA L).eval x = syntacticMorphism L (FreeMonoid.ofList x) := by
  rw [DFA.eval, syntacticDFA_evalFrom, syntacticDFA_start, one_mul]

/-- **The syntactic DFA accepts its language.** For every language $L$, the syntactic DFA of $L$
accepts exactly $L$. -/
theorem syntacticDFA_accepts (L : Language Symbol) : (syntacticDFA L).accepts = L := by
  ext x
  rw [DFA.mem_accepts, syntacticDFA_eval]
  exact syntacticMorphism_mem_accept L (FreeMonoid.ofList x)

/-- **The syntactic DFA is accessible.** For every language $L$, every state of the syntactic DFA
of $L$ is reachable: some word leads to it from the start state. -/
theorem syntacticDFA_accessible (L : Language Symbol) : Accessible (syntacticDFA L) := by
  intro q
  obtain ⟨x, rfl⟩ := syntacticMorphism_surjective L q
  exact ⟨FreeMonoid.toList x, by simp⟩

/-- **Finite syntactic monoid implies regularity.** Every language whose syntactic monoid is
finite is regular. -/
theorem isRegular_of_finite_syntacticMonoid (L : Language Symbol)
    [Finite (SyntacticMonoid L)] : L.IsRegular := by
  classical
  let _ : Fintype (SyntacticMonoid L) := Fintype.ofFinite _
  rw [_root_.Language.isRegular_iff]
  exact ⟨SyntacticMonoid L, inferInstance, syntacticDFA L, syntacticDFA_accepts L⟩

/-- **The syntactic DFA of a language with finite syntactic monoid.** If the syntactic monoid of a
language $L$ is finite, then the syntactic DFA of $L$ has finitely many states and accepts exactly
$L$.

This gives a specific finite recognizer, the syntactic DFA, rather than merely the existence of
some finite DFA. -/
theorem exists_finite_syntacticDFA (L : Language Symbol) [Finite (SyntacticMonoid L)] :
    ∃ _ : Fintype (SyntacticMonoid L), (syntacticDFA L).accepts = L := by
  classical
  exact ⟨Fintype.ofFinite _, syntacticDFA_accepts L⟩

/-- **The transition morphism of a DFA recognizes its language.** Let $M$ be a DFA over an
alphabet $\Sigma$ with state set $Q$, start state $q_0$ and set of accepting states $F$. The
transition morphism of $M$, from the free monoid $\Sigma^*$ to the monoid of state
transformations of $Q$, recognizes the language accepted by $M$ through the set of
transformations $f$ with $f(q_0) \in F$.

No accessibility or state-separation hypothesis on $M$ is needed. -/
theorem recognizes_transitionMorphism (M : DFA Symbol State) :
    Recognizes M.accepts (transitionMorphism M) {f | f M.start ∈ M.accept} := by
  intro x
  rfl

/-- **Languages of finite automata have finite syntactic monoids.** Every language accepted by a
DFA with finitely many states has a finite syntactic monoid. -/
theorem finite_syntacticMonoid_of_finite_dfa (M : DFA Symbol State)
    [Finite State] : Finite (SyntacticMonoid M.accepts) := by
  classical
  let _ : Fintype State := Fintype.ofFinite State
  let _ : Fintype (StateTransformation State) :=
    Fintype.ofEquiv (State → State) stateTransformationEquiv.symm
  exact finite_syntacticMonoid_of_recognizer (transitionMorphism M)
    {f | f M.start ∈ M.accept} (recognizes_transitionMorphism M)

end Cslib.Language
