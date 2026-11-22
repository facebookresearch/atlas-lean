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

/-- A monoid morphism recognizes `L` through `accept` when membership of every word is exactly
membership of its image in `accept`. -/
def Recognizes [Monoid Carrier] (L : Language Symbol) (morphism : FreeMonoid Symbol →* Carrier)
    (accept : Set Carrier) : Prop :=
  ∀ x, FreeMonoid.toList x ∈ L ↔ morphism x ∈ accept

theorem Recognizes.mem_iff [Monoid Carrier] {L : Language Symbol}
    {morphism : FreeMonoid Symbol →* Carrier} {accept : Set Carrier}
    (h : Recognizes L morphism accept) (x : FreeMonoid Symbol) :
    FreeMonoid.toList x ∈ L ↔ morphism x ∈ accept :=
  h x

/-- The canonical syntactic morphism recognizes its language. -/
theorem recognizes_syntacticMorphism (L : Language Symbol) :
    Recognizes L (syntacticMorphism L) (syntacticAccept L) :=
  syntacticMorphism_mem_accept L

/-- A recognizing morphism remains a recognizer after pulling its accepting set back along a
factorization. -/
theorem Recognizes.comp [Monoid Carrier] {Target : Type*} [Monoid Target]
    {L : Language Symbol} {morphism : FreeMonoid Symbol →* Carrier} {accept : Set Carrier}
    (h : Recognizes L morphism accept) (factor : Target →* Carrier)
    (source : FreeMonoid Symbol →* Target) (hfactor : factor.comp source = morphism) :
    Recognizes L source (factor ⁻¹' accept) := by
  intro x
  rw [h x]
  change morphism x ∈ accept ↔ factor (source x) ∈ accept
  rw [← MonoidHom.comp_apply, hfactor]

/-- Equal images under a recognizing morphism cannot be distinguished by a two-sided context. -/
theorem syntacticRel_of_recognizer_eq [Monoid Carrier] {L : Language Symbol}
    {morphism : FreeMonoid Symbol →* Carrier} {accept : Set Carrier}
    (hrec : Recognizes L morphism accept) {x y : FreeMonoid Symbol}
    (hxy : morphism x = morphism y) : syntacticRel L x y := by
  intro u v
  rw [hrec, hrec]
  simp only [map_mul]
  rw [hxy]

/-- The kernel of every recognizing morphism refines the syntactic congruence. -/
theorem recognizer_ker_le_syntacticCon [Monoid Carrier] {L : Language Symbol}
    {morphism : FreeMonoid Symbol →* Carrier} {accept : Set Carrier}
    (hrec : Recognizes L morphism accept) : Con.ker morphism ≤ syntacticCon L := by
  intro x y hxy
  exact syntacticRel_of_recognizer_eq hrec hxy

/-- The quotient by the kernel of a recognizing morphism maps canonically to the syntactic
monoid.  This is the algebraic minimality map before identifying the kernel quotient with the
image of the recognizer. -/
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

/-- The canonical map from a recognizer's kernel quotient onto the syntactic monoid is
surjective. -/
theorem recognizerQuotientToSyntactic_surjective [Monoid Carrier] {L : Language Symbol}
    (morphism : FreeMonoid Symbol →* Carrier) (accept : Set Carrier)
    (hrec : Recognizes L morphism accept) :
    Function.Surjective (recognizerQuotientToSyntactic morphism accept hrec) := by
  intro q
  obtain ⟨x, rfl⟩ := syntacticMorphism_surjective L q
  exact ⟨(Con.ker morphism).mk' x, recognizerQuotientToSyntactic_mk morphism accept hrec x⟩

/-- The image of a recognizing morphism maps canonically onto the syntactic monoid. -/
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

/-- The image of any recognizing morphism surjects onto the syntactic monoid. -/
theorem recognizerImageToSyntactic_surjective [Monoid Carrier] {L : Language Symbol}
    (morphism : FreeMonoid Symbol →* Carrier) (accept : Set Carrier)
    (hrec : Recognizes L morphism accept) :
    Function.Surjective (recognizerImageToSyntactic morphism accept hrec) := by
  intro q
  obtain ⟨x, rfl⟩ := syntacticMorphism_surjective L q
  exact ⟨⟨morphism x, ⟨x, rfl⟩⟩,
    recognizerImageToSyntactic_image morphism accept hrec x⟩

/-- If the carrier of a recognizing monoid is finite, then so is the syntactic monoid. -/
theorem finite_syntacticMonoid_of_recognizer [Monoid Carrier] [Finite Carrier]
    {L : Language Symbol} (morphism : FreeMonoid Symbol →* Carrier) (accept : Set Carrier)
    (hrec : Recognizes L morphism accept) : Finite (SyntacticMonoid L) := by
  let _ : Finite (MonoidHom.mrange morphism) := Subtype.finite
  exact Finite.of_surjective (recognizerImageToSyntactic morphism accept hrec)
    (recognizerImageToSyntactic_surjective morphism accept hrec)

/-- Recognition can be stated using equality with the inverse image of the accepting set. -/
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

/-- A recognizer is unchanged when its accepting subset agrees on the image of the morphism. -/
theorem Recognizes.congr_accept [Monoid Carrier] {L : Language Symbol}
    {morphism : FreeMonoid Symbol →* Carrier} {accept₁ accept₂ : Set Carrier}
    (hrec : Recognizes L morphism accept₁)
    (haccept : ∀ x, morphism x ∈ accept₁ ↔ morphism x ∈ accept₂) :
    Recognizes L morphism accept₂ := by
  intro x
  exact (hrec x).trans (haccept x)

/-! ## The canonical syntactic automaton -/

/-- The DFA whose states are syntactic classes and whose transitions multiply by letter
classes.  It is the direct automata-theoretic presentation of the canonical syntactic
recognizer. -/
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

/-- Evaluation in the syntactic DFA is multiplication by the syntactic class of the input. -/
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

/-- The syntactic DFA accepts exactly the language from which it was constructed. -/
theorem syntacticDFA_accepts (L : Language Symbol) : (syntacticDFA L).accepts = L := by
  ext x
  rw [DFA.mem_accepts, syntacticDFA_eval]
  exact syntacticMorphism_mem_accept L (FreeMonoid.ofList x)

/-- Every state of the syntactic DFA is reachable. -/
theorem syntacticDFA_accessible (L : Language Symbol) : Accessible (syntacticDFA L) := by
  intro q
  obtain ⟨x, rfl⟩ := syntacticMorphism_surjective L q
  exact ⟨FreeMonoid.toList x, by simp⟩

/-- A language with finite syntactic monoid is regular. -/
theorem isRegular_of_finite_syntacticMonoid (L : Language Symbol)
    [Finite (SyntacticMonoid L)] : L.IsRegular := by
  classical
  let _ : Fintype (SyntacticMonoid L) := Fintype.ofFinite _
  rw [_root_.Language.isRegular_iff]
  exact ⟨SyntacticMonoid L, inferInstance, syntacticDFA L, syntacticDFA_accepts L⟩

/-- Finiteness of the syntactic monoid is sufficient for a finite canonical recognizer, rather
than merely for the existence of some finite DFA. -/
theorem exists_finite_syntacticDFA (L : Language Symbol) [Finite (SyntacticMonoid L)] :
    ∃ _ : Fintype (SyntacticMonoid L), (syntacticDFA L).accepts = L := by
  classical
  exact ⟨Fintype.ofFinite _, syntacticDFA_accepts L⟩

/-- The transition morphism recognizes the language accepted by its DFA, without requiring
accessibility or state separation. -/
theorem recognizes_transitionMorphism (M : DFA Symbol State) :
    Recognizes M.accepts (transitionMorphism M) {f | f M.start ∈ M.accept} := by
  intro x
  rfl

/-- Every language recognized by a finite-state DFA has a finite syntactic monoid. -/
theorem finite_syntacticMonoid_of_finite_dfa (M : DFA Symbol State)
    [Finite State] : Finite (SyntacticMonoid M.accepts) := by
  classical
  let _ : Fintype State := Fintype.ofFinite State
  let _ : Fintype (StateTransformation State) :=
    Fintype.ofEquiv (State → State) stateTransformationEquiv.symm
  exact finite_syntacticMonoid_of_recognizer (transitionMorphism M)
    {f | f M.start ∈ M.accept} (recognizes_transitionMorphism M)

end Cslib.Language
