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

public import CSLibExt.Computability.Languages.Congruences.Universal
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.GroupTheory.Congruence.Basic

/-!
# Syntactic congruences and syntactic monoids

The Nerode relation compares words by their possible right continuations.  The syntactic
congruence strengthens this test by allowing arbitrary left and right contexts.  It is therefore
a monoid congruence on the free monoid of words.  Its quotient is the syntactic monoid of the
language.

This file develops the context relation, its quotient monoid, the canonical recognizing morphism,
and its connection with deterministic automata.  In particular, the syntactic class of a word is
determined by its action on the states of the residual-language DFA.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v

variable {Symbol : Type u} {State : Type v}

/-- **Syntactic equivalence.** Let $L$ be a language over an alphabet $\Sigma$. Two words
$x, y \in \Sigma^*$ are syntactically equivalent for $L$ when, for all words $u, v \in \Sigma^*$,
$uxv \in L$ if and only if $uyv \in L$. -/
def syntacticRel (L : Language Symbol) (x y : FreeMonoid Symbol) : Prop :=
  ∀ u v, FreeMonoid.toList (u * x * v) ∈ L ↔ FreeMonoid.toList (u * y * v) ∈ L

@[refl]
theorem syntacticRel_refl (L : Language Symbol) (x : FreeMonoid Symbol) : syntacticRel L x x :=
  fun _ _ ↦ Iff.rfl

@[symm]
theorem syntacticRel_symm (L : Language Symbol) {x y : FreeMonoid Symbol} :
    syntacticRel L x y → syntacticRel L y x :=
  fun h u v ↦ (h u v).symm

@[trans]
theorem syntacticRel_trans (L : Language Symbol) {x y z : FreeMonoid Symbol} :
    syntacticRel L x y → syntacticRel L y z → syntacticRel L x z :=
  fun hxy hyz u v ↦ (hxy u v).trans (hyz u v)

/-- **Syntactic equivalence is stable under left multiplication.** Let $L$ be a language over an
alphabet $\Sigma$. If two words $x, y \in \Sigma^*$ are syntactically equivalent for $L$, then
for every word $w \in \Sigma^*$ the words $wx$ and $wy$ are syntactically equivalent for $L$. -/
theorem syntacticRel_prefix (L : Language Symbol) {x y : FreeMonoid Symbol}
    (h : syntacticRel L x y) (w : FreeMonoid Symbol) : syntacticRel L (w * x) (w * y) := by
  intro u v
  simpa only [mul_assoc] using h (u * w) v

/-- **Syntactic equivalence is stable under right multiplication.** Let $L$ be a language over an
alphabet $\Sigma$. If two words $x, y \in \Sigma^*$ are syntactically equivalent for $L$, then
for every word $w \in \Sigma^*$ the words $xw$ and $yw$ are syntactically equivalent for $L$. -/
theorem syntacticRel_suffix (L : Language Symbol) {x y : FreeMonoid Symbol}
    (h : syntacticRel L x y) (w : FreeMonoid Symbol) : syntacticRel L (x * w) (y * w) := by
  intro u v
  simpa only [mul_assoc] using h u (w * v)

/-- **Syntactic equivalence is compatible with concatenation.** Let $L$ be a language over an
alphabet $\Sigma$ and let $w, x, y, z \in \Sigma^*$ be words. If $w$ and $x$ are syntactically
equivalent for $L$, and $y$ and $z$ are syntactically equivalent for $L$, then $wy$ and $xz$ are
syntactically equivalent for $L$. -/
theorem syntacticRel_append (L : Language Symbol) {w x y z : FreeMonoid Symbol}
    (h₁ : syntacticRel L w x) (h₂ : syntacticRel L y z) :
    syntacticRel L (w * y) (x * z) :=
  syntacticRel_trans L (syntacticRel_suffix L h₁ y) (syntacticRel_prefix L h₂ x)

/-- **Syntactic congruence.** For a language $L$ over an alphabet $\Sigma$, the syntactic
congruence of $L$ is the monoid congruence on the free monoid $\Sigma^*$ that relates words $x$
and $y$ when, for all words $u$ and $v$, $uxv \in L$ if and only if $uyv \in L$. -/
def syntacticCon (L : Language Symbol) : Con (FreeMonoid Symbol) where
  r := syntacticRel L
  iseqv := ⟨syntacticRel_refl L, syntacticRel_symm L, syntacticRel_trans L⟩
  mul' := syntacticRel_append L

@[simp]
theorem syntacticCon_apply (L : Language Symbol) (x y : FreeMonoid Symbol) :
    syntacticCon L x y ↔ syntacticRel L x y :=
  Iff.rfl

/-- **Syntactic monoid.** For a language $L$ over an alphabet $\Sigma$, the syntactic monoid of
$L$ is the quotient of the free monoid $\Sigma^*$ of words by the syntactic congruence of $L$,
which relates words $x$ and $y$ when $uxv \in L \iff uyv \in L$ for all words $u$ and $v$. -/
abbrev SyntacticMonoid (L : Language Symbol) := (syntacticCon L).Quotient

/-- **Syntactic morphism.** For a language $L$ over an alphabet $\Sigma$, the syntactic morphism
of $L$ is the monoid homomorphism from the free monoid $\Sigma^*$ of words to the syntactic
monoid of $L$ that sends each word to its class under the syntactic congruence of $L$. -/
def syntacticMorphism (L : Language Symbol) : FreeMonoid Symbol →* SyntacticMonoid L :=
  Con.mk' (syntacticCon L)

@[simp]
theorem syntacticMorphism_apply (L : Language Symbol) (x : FreeMonoid Symbol) :
    syntacticMorphism L x = (x : SyntacticMonoid L) :=
  rfl

theorem syntacticMorphism_surjective (L : Language Symbol) :
    Function.Surjective (syntacticMorphism L) :=
  Con.mk'_surjective

theorem syntacticMorphism_eq_iff (L : Language Symbol) (x y : FreeMonoid Symbol) :
    syntacticMorphism L x = syntacticMorphism L y ↔ syntacticRel L x y := by
  exact Quotient.eq''

/-- **Syntactically equivalent words agree on membership.** Let $L$ be a language over an
alphabet $\Sigma$. If two words $x, y \in \Sigma^*$ are syntactically equivalent for $L$, then
$x \in L$ if and only if $y \in L$. -/
theorem syntacticRel_mem_iff (L : Language Symbol) {x y : FreeMonoid Symbol}
    (h : syntacticRel L x y) : FreeMonoid.toList x ∈ L ↔ FreeMonoid.toList y ∈ L := by
  simpa using h 1 1

/-- **Accepting set of the syntactic monoid.** For a language $L$, the accepting set of the
syntactic monoid of $L$ is the set of syntactic classes of words of $L$: a class belongs to it
when its representatives lie in $L$, which does not depend on the representative chosen. -/
def syntacticAccept (L : Language Symbol) : Set (SyntacticMonoid L) :=
  {q | Con.liftOn q (fun x ↦ FreeMonoid.toList x ∈ L)
    (fun _ _ h ↦ propext (syntacticRel_mem_iff L h))}

@[simp]
theorem syntacticMorphism_mem_accept (L : Language Symbol) (x : FreeMonoid Symbol) :
    syntacticMorphism L x ∈ syntacticAccept L ↔ FreeMonoid.toList x ∈ L :=
  Iff.rfl

/-- **The syntactic morphism recognizes the language.** Let $L$ be a language over an alphabet
$\Sigma$. For every word $x \in \Sigma^*$, $x \in L$ if and only if the image of $x$ under the
syntactic morphism of $L$ lies in the accepting set of the syntactic monoid of $L$, the set of
syntactic classes of words of $L$. -/
theorem mem_iff_syntacticMorphism_mem (L : Language Symbol) (x : FreeMonoid Symbol) :
    FreeMonoid.toList x ∈ L ↔ syntacticMorphism L x ∈ syntacticAccept L :=
  (syntacticMorphism_mem_accept L x).symm

/-- **Syntactic equivalence refines Nerode equivalence.** Let $L$ be a language over an alphabet
$\Sigma$. If two words $x, y \in \Sigma^*$ are syntactically equivalent for $L$, then they are
Nerode equivalent for $L$: the sets $\{z : xz \in L\}$ and $\{z : yz \in L\}$ are equal. -/
theorem syntacticRel_nerodeRel (L : Language Symbol) {x y : FreeMonoid Symbol}
    (h : syntacticRel L x y) : nerodeRel L (FreeMonoid.toList x) (FreeMonoid.toList y) := by
  rw [nerodeRel_iff]
  intro z
  simpa using h 1 (FreeMonoid.ofList z)

/-- **Equal syntactic classes give equal Nerode classes.** Let $L$ be a language. For all words
$x$ and $y$, if the syntactic morphism of $L$ sends $x$ and $y$ to the same element of the
syntactic monoid of $L$, then $x$ and $y$ have the same Nerode class with respect to $L$. -/
theorem nerodeClass_eq_of_syntacticMorphism_eq (L : Language Symbol) {x y : FreeMonoid Symbol}
    (h : syntacticMorphism L x = syntacticMorphism L y) :
    nerodeClass L (FreeMonoid.toList x) = nerodeClass L (FreeMonoid.toList y) := by
  rw [nerodeClass_eq_iff]
  exact syntacticRel_nerodeRel L ((syntacticMorphism_eq_iff L x y).mp h)

/-- **Transition action of a word.** For a DFA $M$ and a word $x$, the transition action of $x$ is
the map sending each state $q$ of $M$ to the state that $M$ reaches by reading $x$ starting
from $q$. -/
def transitionAction (M : DFA Symbol State) (x : FreeMonoid Symbol) : State → State :=
  fun q ↦ M.evalFrom q (FreeMonoid.toList x)

@[simp]
theorem transitionAction_nil (M : DFA Symbol State) : transitionAction M 1 = id := by
  ext q
  rfl

theorem transitionAction_append (M : DFA Symbol State) (x y : FreeMonoid Symbol) :
    transitionAction M (x * y) = transitionAction M y ∘ transitionAction M x := by
  ext q
  exact DFA.evalFrom_of_append M q (FreeMonoid.toList x) (FreeMonoid.toList y)

/-- **Words with the same transition action are syntactically equivalent.** Let $M$ be a DFA over
an alphabet $\Sigma$ and let $L$ be the language accepted by $M$. If two words
$x, y \in \Sigma^*$ have the same transition action on $M$, that is, for every state $q$, running
$M$ from $q$ on $x$ ends in the same state as running $M$ from $q$ on $y$, then $x$ and $y$ are
syntactically equivalent for $L$. -/
theorem syntacticRel_of_transitionAction_eq (M : DFA Symbol State) {x y : FreeMonoid Symbol}
    (h : transitionAction M x = transitionAction M y) : syntacticRel M.accepts x y := by
  intro u v
  simp only [FreeMonoid.toList_mul, DFA.mem_accepts, DFA.eval, List.append_assoc,
    DFA.evalFrom_of_append]
  have hxy : M.evalFrom (M.evalFrom M.start (FreeMonoid.toList u)) (FreeMonoid.toList x) =
      M.evalFrom (M.evalFrom M.start (FreeMonoid.toList u)) (FreeMonoid.toList y) := by
    exact congrFun h (M.evalFrom M.start (FreeMonoid.toList u))
  rw [hxy]

/-- **Syntactically equivalent words act identically.** Let $M$ be a DFA that is accessible
(every state is reachable from the start state) and state-separated (two states with the same
continuation language are equal). If two words $x$ and $y$ are syntactically equivalent for the
language accepted by $M$, then $x$ and $y$ have the same transition action on $M$: for every
state $q$, reading $x$ from $q$ and reading $y$ from $q$ lead to the same state. -/
theorem transitionAction_eq_of_syntacticRel (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) {x y : FreeMonoid Symbol} (h : syntacticRel M.accepts x y) :
    transitionAction M x = transitionAction M y := by
  funext q
  apply hsep
  obtain ⟨u, rfl⟩ := hacc q
  rw [stateEquivalent_iff]
  intro v
  simpa only [transitionAction, FreeMonoid.toList_mul, FreeMonoid.toList_ofList, DFA.eval,
    DFA.mem_accepts, DFA.evalFrom_of_append, List.append_assoc] using
    h (FreeMonoid.ofList u) (FreeMonoid.ofList v)

/-- **Syntactic equivalence via transition actions.** Let $M$ be a DFA over an alphabet $\Sigma$
that is accessible (every state is reached from the start state by some word) and
state-separated (distinct states have distinct continuation languages), and let $L$ be the
language accepted by $M$. Then two words $x, y \in \Sigma^*$ are syntactically equivalent for $L$
if and only if they have the same transition action on $M$: for every state $q$, running $M$
from $q$ on $x$ ends in the same state as running $M$ from $q$ on $y$. -/
theorem syntacticRel_iff_transitionAction_eq (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) (x y : FreeMonoid Symbol) :
    syntacticRel M.accepts x y ↔ transitionAction M x = transitionAction M y :=
  ⟨transitionAction_eq_of_syntacticRel M hacc hsep,
    syntacticRel_of_transitionAction_eq M⟩

/-! ## Transition monoids -/

/-- **State transformation monoid.** For a type $Q$ of states, the state transformation monoid
of $Q$ consists of all functions $Q \to Q$, multiplied by composition in the opposite order: the
product $fg$ first applies $f$ and then $g$, so $(fg)(q) = g(f(q))$, and the unit is the
identity function. -/
abbrev StateTransformation (State : Type v) := (Function.End State)ᵐᵒᵖ

instance : CoeFun (StateTransformation State) (fun _ ↦ State → State) :=
  ⟨fun f ↦ MulOpposite.unop f⟩

@[ext]
theorem StateTransformation.ext {f g : StateTransformation State}
    (h : ∀ q, f q = g q) : f = g := by
  exact MulOpposite.unop_injective (funext h)

/-- **State transformations as functions.** For a type $Q$ of states, the bijection from the
state transformations of $Q$ to the functions $Q \to Q$ that sends each transformation to its
underlying function; it forgets the multiplication of state transformations. -/
def stateTransformationEquiv : StateTransformation State ≃ (State → State) where
  toFun f := MulOpposite.unop f
  invFun f := MulOpposite.op f
  left_inv := MulOpposite.op_unop
  right_inv := MulOpposite.unop_op

@[simp]
theorem StateTransformation.one_apply (q : State) :
    (1 : StateTransformation State) q = q :=
  rfl

@[simp]
theorem StateTransformation.mul_apply (f g : StateTransformation State) (q : State) :
    (f * g) q = g (f q) :=
  rfl

/-- **Transition transformation of a word.** For a DFA $M$ and a word $x$, the transition
transformation of $x$ is the transition action of $x$, the map sending each state $q$ to the
state that $M$ reaches by reading $x$ from $q$, regarded as an element of the monoid of state
transformations of $M$ (multiplied in reading order: $fg$ applies $f$ first, then $g$). -/
def transitionTransformation (M : DFA Symbol State) (x : FreeMonoid Symbol) :
    StateTransformation State :=
  MulOpposite.op (transitionAction M x)

@[simp]
theorem transitionTransformation_apply (M : DFA Symbol State) (x : FreeMonoid Symbol)
    (q : State) : transitionTransformation M x q = M.evalFrom q (FreeMonoid.toList x) :=
  rfl

@[simp]
theorem transitionTransformation_one (M : DFA Symbol State) :
    transitionTransformation M 1 = 1 := by
  ext q
  rfl

@[simp]
theorem transitionTransformation_mul (M : DFA Symbol State) (x y : FreeMonoid Symbol) :
    transitionTransformation M (x * y) =
      transitionTransformation M x * transitionTransformation M y := by
  ext q
  exact DFA.evalFrom_of_append M q (FreeMonoid.toList x) (FreeMonoid.toList y)

/-- **Transition morphism of a DFA.** For a DFA $M$, the transition morphism is the monoid
homomorphism from the free monoid of words to the state transformations of $M$ that sends each
word $x$ to its transition action, the map taking each state $q$ to the state that $M$ reaches
by reading $x$ from $q$. State transformations are multiplied in reading order, so the product
$fg$ applies $f$ first and then $g$; with this order, the word $xy$ is sent to the product of
the images of $x$ and $y$. -/
def transitionMorphism (M : DFA Symbol State) :
    FreeMonoid Symbol →* StateTransformation State where
  toFun := transitionTransformation M
  map_one' := transitionTransformation_one M
  map_mul' := transitionTransformation_mul M

@[simp]
theorem transitionMorphism_apply (M : DFA Symbol State) (x : FreeMonoid Symbol) :
    transitionMorphism M x = transitionTransformation M x :=
  rfl

/-- **Transition monoid of a DFA.** The transition monoid of a DFA $M$ is the image of the
transition morphism of $M$: the submonoid of state transformations of $M$ consisting of the
transition actions of all words, where a word $x$ acts by sending each state $q$ to the state
that $M$ reaches by reading $x$ from $q$. State transformations are multiplied in reading
order, so the product $fg$ applies $f$ first and then $g$. -/
def TransitionMonoid (M : DFA Symbol State) := MonoidHom.mrange (transitionMorphism M)

/-- **Transition monoid element of a word.** Let $M$ be a DFA over an alphabet $\Sigma$. Each word
$x \in \Sigma^*$ determines the element of the transition monoid of $M$ given by the state
transformation that sends each state $q$ to the state $M$ reaches from $q$ after reading $x$. -/
def toTransitionMonoid (M : DFA Symbol State) (x : FreeMonoid Symbol) : TransitionMonoid M :=
  ⟨transitionMorphism M x, ⟨x, rfl⟩⟩

@[simp]
theorem toTransitionMonoid_val (M : DFA Symbol State) (x : FreeMonoid Symbol) :
    (toTransitionMonoid M x).val = transitionMorphism M x :=
  rfl

theorem toTransitionMonoid_surjective (M : DFA Symbol State) :
    Function.Surjective (toTransitionMonoid M) := by
  rintro ⟨f, x, rfl⟩
  exact ⟨x, rfl⟩

theorem toTransitionMonoid_eq_iff (M : DFA Symbol State) (x y : FreeMonoid Symbol) :
    toTransitionMonoid M x = toTransitionMonoid M y ↔
      transitionAction M x = transitionAction M y := by
  rw [Subtype.ext_iff]
  constructor
  · intro h
    exact congrArg MulOpposite.unop h
  · intro h
    exact StateTransformation.ext (congrFun h)

theorem transitionMorphism_eq_iff (M : DFA Symbol State) (x y : FreeMonoid Symbol) :
    transitionMorphism M x = transitionMorphism M y ↔
      transitionAction M x = transitionAction M y := by
  constructor
  · intro h
    exact congrArg MulOpposite.unop h
  · intro h
    exact StateTransformation.ext (congrFun h)

/-- **Syntactic congruence as a kernel.** Let $M$ be an accessible, state-separated DFA and let
$L$ be the language $M$ accepts. The syntactic congruence of $L$ equals the kernel of the
transition morphism of $M$: two words are syntactically equivalent for $L$ if and only if they
induce the same transformation of the states of $M$. -/
theorem syntacticCon_eq_transitionMorphism_ker (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) : syntacticCon M.accepts = Con.ker (transitionMorphism M) := by
  apply Con.ext
  intro x y
  rw [syntacticCon_apply, Con.ker_rel]
  exact (syntacticRel_iff_transitionAction_eq M hacc hsep x y).trans
    (transitionMorphism_eq_iff M x y).symm

/-- **Action of the syntactic monoid on states.** Let $M$ be an accessible, state-separated DFA
with state type $Q$, and let $L$ be the language $M$ accepts. This is the monoid homomorphism
from the syntactic monoid of $L$ to the state transformation monoid of $Q$ that sends the
syntactic class of each word $x$ to the map taking each state $q$ to the state $M$ reaches from
$q$ by reading $x$. It is well defined because syntactically equivalent words act identically on
the states of such a DFA. -/
def syntacticActionHom (M : DFA Symbol State) (hacc : Accessible M) (hsep : StateSeparated M) :
    SyntacticMonoid M.accepts →* StateTransformation State :=
  (syntacticCon M.accepts).lift (transitionMorphism M) <| by
    intro x y hxy
    exact (transitionMorphism_eq_iff M x y).mpr <|
      (syntacticRel_iff_transitionAction_eq M hacc hsep x y).mp hxy

@[simp]
theorem syntacticActionHom_mk (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) (x : FreeMonoid Symbol) :
    syntacticActionHom M hacc hsep (syntacticMorphism M.accepts x) = transitionMorphism M x :=
  Con.lift_mk' _ _

theorem syntacticActionHom_injective (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) : Function.Injective (syntacticActionHom M hacc hsep) := by
  intro p q hpq
  induction p using Con.induction_on with
  | _ x =>
    induction q using Con.induction_on with
    | _ y =>
      apply (syntacticMorphism_eq_iff M.accepts x y).mpr
      apply (syntacticRel_iff_transitionAction_eq M hacc hsep x y).mpr
      change syntacticActionHom M hacc hsep (syntacticMorphism M.accepts x) =
        syntacticActionHom M hacc hsep (syntacticMorphism M.accepts y) at hpq
      rw [syntacticActionHom_mk, syntacticActionHom_mk] at hpq
      exact (transitionMorphism_eq_iff M x y).mp hpq

/-- **Image of the syntactic action.** Let $M$ be an accessible, state-separated DFA and let $L$
be the language $M$ accepts. The image of the action of the syntactic monoid of $L$ on the states
of $M$, the monoid homomorphism sending the syntactic class of each word $x$ to the state
transformation induced by reading $x$, is exactly the transition monoid of $M$. -/
theorem syntacticActionHom_range (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) :
    MonoidHom.mrange (syntacticActionHom M hacc hsep) = TransitionMonoid M := by
  ext f
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Con.induction_on with
    | _ x => exact ⟨x, syntacticActionHom_mk M hacc hsep x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨syntacticMorphism M.accepts x, (syntacticActionHom_mk M hacc hsep x).symm⟩

end Cslib.Language
