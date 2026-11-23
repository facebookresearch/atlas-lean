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

public import Mathlib.Computability.MyhillNerode

/-!
# Nerode equivalence and the canonical quotient automaton

This file develops the word-equivalence formulation of the Myhill--Nerode theorem. Two words are
equivalent when no continuation distinguishes their membership in the language. The equivalence is
stable under appending a common continuation, so its quotient carries a canonical deterministic
automaton.

Mathlib's `Language.toDFA` uses left quotients directly as states. Here we expose the corresponding
quotient of words, prove it equivalent to the range of left quotients, and construct the canonical
automaton on equivalence classes.

## Main definitions

* `Cslib.Language.nerodeRel`: indistinguishability by continuations.
* `Cslib.Language.nerodeSetoid`: the induced equivalence relation on words.
* `Cslib.Language.NerodeClass`: equivalence classes of words.
* `Cslib.Language.nerodeDFA`: the canonical DFA on Nerode classes.

## Main results

* `nerodeRel_iff`: the continuation characterization.
* `nerodeRel_append_right`: Nerode equivalence is a right congruence.
* `nerodeClassEquivResidual`: classes are equivalent to reachable left quotients.
* `accepts_nerodeDFA`: the canonical quotient automaton recognizes the original language.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u

variable {Symbol : Type u} {L : Language Symbol}

/-- **Nerode equivalence.** Let $L$ be a language over an alphabet $\Sigma$. Two words
$x, y \in \Sigma^*$ are Nerode equivalent for $L$ when they have the same left quotient, that is,
$\{z \in \Sigma^* \mid xz \in L\} = \{z \in \Sigma^* \mid yz \in L\}$. -/
def nerodeRel (L : Language Symbol) (x y : List Symbol) : Prop :=
  L.leftQuotient x = L.leftQuotient y

@[refl]
theorem nerodeRel_refl (L : Language Symbol) (x : List Symbol) : nerodeRel L x x :=
  rfl

@[symm]
theorem nerodeRel_symm {x y : List Symbol} (h : nerodeRel L x y) : nerodeRel L y x :=
  h.symm

@[trans]
theorem nerodeRel_trans {x y z : List Symbol} (hxy : nerodeRel L x y)
    (hyz : nerodeRel L y z) : nerodeRel L x z :=
  hxy.trans hyz

/-- **The Nerode setoid.** For a language $L$ over an alphabet $\Sigma$, the Nerode setoid of $L$
is the set $\Sigma^*$ of words equipped with Nerode equivalence for $L$, which is reflexive,
symmetric and transitive. -/
def nerodeSetoid (L : Language Symbol) : Setoid (List Symbol) where
  r := nerodeRel L
  iseqv := ⟨nerodeRel_refl L, nerodeRel_symm, nerodeRel_trans⟩

/-- **Nerode classes.** For a language $L$ over an alphabet $\Sigma$, the Nerode classes of $L$
are the elements of the quotient of the set of words over $\Sigma$ by Nerode equivalence for
$L$, under which two words $x$ and $y$ are equivalent when they have the same left quotient,
that is, when for every word $z$ we have $xz \in L$ if and only if $yz \in L$. -/
abbrev NerodeClass (L : Language Symbol) := Quotient (nerodeSetoid L)

/-- **Continuation characterization of Nerode equivalence.** Let $L$ be a language over an
alphabet $\Sigma$. Two words $x, y \in \Sigma^*$ are Nerode equivalent for $L$ if and only if,
for every word $z \in \Sigma^*$, $xz \in L$ holds exactly when $yz \in L$. -/
theorem nerodeRel_iff {x y : List Symbol} :
    nerodeRel L x y ↔ ∀ z, x ++ z ∈ L ↔ y ++ z ∈ L := by
  constructor
  · intro h z
    exact Set.ext_iff.mp h z
  · intro h
    exact Set.ext fun z ↦ h z

/-- **Nerode equivalent words agree on membership.** Let $L$ be a language. If two words $x$ and
$y$ are Nerode equivalent for $L$, then $x \in L$ if and only if $y \in L$. -/
theorem nerodeRel.mem_iff {x y : List Symbol} (h : nerodeRel L x y) : x ∈ L ↔ y ∈ L := by
  simpa using (nerodeRel_iff.mp h [])

/-- **Nerode equivalence is a right congruence.** Let $L$ be a language over an alphabet
$\Sigma$. If two words $x, y \in \Sigma^*$ are Nerode equivalent for $L$, then for every word
$z \in \Sigma^*$ the words $xz$ and $yz$ are Nerode equivalent for $L$. -/
theorem nerodeRel_append_right {x y : List Symbol} (h : nerodeRel L x y)
    (z : List Symbol) : nerodeRel L (x ++ z) (y ++ z) := by
  unfold nerodeRel at h ⊢
  rw [L.leftQuotient_append, L.leftQuotient_append, h]

/-- **Appending a symbol preserves Nerode equivalence.** Let $L$ be a language over an alphabet
$\Sigma$. If two words $x, y \in \Sigma^*$ are Nerode equivalent for $L$, then for every symbol
$a \in \Sigma$ the words $xa$ and $ya$ are Nerode equivalent for $L$. -/
theorem nerodeRel_append_singleton {x y : List Symbol} (h : nerodeRel L x y)
    (a : Symbol) : nerodeRel L (x ++ [a]) (y ++ [a]) :=
  nerodeRel_append_right h [a]

/-- **Appending the empty word preserves the Nerode class.** Let $L$ be a language over an
alphabet $\Sigma$. For every word $x \in \Sigma^*$, the word $x\varepsilon$ obtained by appending
the empty word $\varepsilon$ is Nerode equivalent to $x$ for $L$. -/
@[simp]
theorem nerodeRel_append_nil (x : List Symbol) : nerodeRel L (x ++ []) x := by
  simpa using nerodeRel_refl L x

/-- **Nerode class of a word.** For a language $L$ and a word $x$, the Nerode class $[x]$ of $x$
is the equivalence class of $x$ under Nerode equivalence for $L$. -/
def nerodeClass (L : Language Symbol) (x : List Symbol) : NerodeClass L :=
  Quotient.mk (nerodeSetoid L) x

@[simp]
theorem nerodeClass_eq_iff {x y : List Symbol} :
    nerodeClass L x = nerodeClass L y ↔ nerodeRel L x y := by
  exact Quotient.eq

/-- **Residual map on Nerode classes.** Let $L$ be a language. The residual map sends the Nerode
class $[x]$ of a word $x$ to the left quotient $x^{-1}L = \{ y \mid xy \in L \}$, viewed as an
element of the set $\{ w^{-1}L \mid w \text{ a word} \}$ of left quotients of $L$. It is
well-defined because Nerode equivalent words have the same left quotient. -/
def classResidual (L : Language Symbol) : NerodeClass L → Set.range L.leftQuotient :=
  Quotient.lift
    (fun x ↦ ⟨L.leftQuotient x, ⟨x, rfl⟩⟩)
    (fun _ _ h ↦ Subtype.ext h)

@[simp]
theorem classResidual_nerodeClass (x : List Symbol) :
    classResidual L (nerodeClass L x) = ⟨L.leftQuotient x, ⟨x, rfl⟩⟩ :=
  rfl

theorem classResidual_injective : Function.Injective (classResidual L) := by
  intro p q h
  induction p using Quotient.inductionOn with
  | _ x =>
    induction q using Quotient.inductionOn with
    | _ y =>
      apply (nerodeClass_eq_iff (L := L)).mpr
      exact Subtype.ext_iff.mp h

theorem classResidual_surjective : Function.Surjective (classResidual L) := by
  rintro ⟨R, x, rfl⟩
  exact ⟨nerodeClass L x, rfl⟩

/-- **Bijection between Nerode classes and left quotients.** For every language $L$, the map
sending the Nerode class $[x]$ of a word $x$ to the left quotient
$x^{-1}L = \{ y \mid xy \in L \}$ is a bijection from the set of Nerode classes of $L$ onto the
set $\{ w^{-1}L \mid w \text{ a word} \}$ of left quotients of $L$. -/
noncomputable def nerodeClassEquivResidual (L : Language Symbol) :
    NerodeClass L ≃ Set.range L.leftQuotient :=
  Equiv.ofBijective (classResidual L) ⟨classResidual_injective, classResidual_surjective⟩

/-- **Transition on Nerode classes.** Let $L$ be a language over an alphabet $\Sigma$ and
$a \in \Sigma$ a symbol. Appending $a$ sends the Nerode class of a word $x$ to the Nerode class
of $xa$; this is well defined because Nerode equivalence is preserved by appending a symbol. -/
def NerodeClass.step (a : Symbol) : NerodeClass L → NerodeClass L :=
  Quotient.map (· ++ [a]) (fun _ _ h ↦ nerodeRel_append_singleton h a)

@[simp]
theorem NerodeClass.step_nerodeClass (x : List Symbol) (a : Symbol) :
    NerodeClass.step (L := L) a (nerodeClass L x) = nerodeClass L (x ++ [a]) :=
  rfl

/-- **Accepting Nerode classes.** Let $L$ be a language. The accepting Nerode classes of $L$ are
those whose words belong to $L$: the Nerode class $[x]$ of a word $x$ is accepting if and only if
$x \in L$. This is well-defined because Nerode equivalent words are either both in $L$ or both
outside $L$. -/
def NerodeClass.Accepting (L : Language Symbol) : Set (NerodeClass L) :=
  {q | Quotient.lift (s := nerodeSetoid L) (fun x ↦ x ∈ L)
    (fun _ _ h ↦ propext (nerodeRel.mem_iff h)) q}

@[simp]
theorem nerodeClass_mem_accepting (x : List Symbol) :
    nerodeClass L x ∈ NerodeClass.Accepting L ↔ x ∈ L :=
  Iff.rfl

/-- **The Nerode automaton.** Let $L$ be a language over an alphabet $\Sigma$. The Nerode
automaton of $L$ is the deterministic automaton over $\Sigma$, not necessarily finite, whose
states are the Nerode classes of words for $L$, whose start state is the class of the empty
word, which on reading a symbol $a \in \Sigma$ moves from the class of a word $x$ to the class
of $xa$, and whose accepting states are the classes of the words in $L$. -/
def nerodeDFA (L : Language Symbol) : DFA Symbol (NerodeClass L) where
  step q a := q.step a
  start := nerodeClass L []
  accept := NerodeClass.Accepting L

@[simp]
theorem nerodeDFA_start : (nerodeDFA L).start = nerodeClass L [] :=
  rfl

@[simp]
theorem nerodeDFA_step (q : NerodeClass L) (a : Symbol) :
    (nerodeDFA L).step q a = q.step a :=
  rfl

theorem nerodeDFA_evalFrom_class (x y : List Symbol) :
    (nerodeDFA L).evalFrom (nerodeClass L x) y = nerodeClass L (x ++ y) := by
  induction y using List.reverseRecOn with
  | nil => simp
  | append_singleton y a ih =>
      simp only [DFA.evalFrom_append_singleton, nerodeDFA_step,
        NerodeClass.step_nerodeClass, ih, List.append_assoc]

@[simp]
theorem nerodeDFA_eval (x : List Symbol) :
    (nerodeDFA L).eval x = nerodeClass L x := by
  simpa [DFA.eval] using nerodeDFA_evalFrom_class (L := L) [] x

/-- **The Nerode automaton recognizes its language.** For every language $L$, the language accepted
by the Nerode automaton of $L$ is exactly $L$. -/
@[simp]
theorem accepts_nerodeDFA : (nerodeDFA L).accepts = L := by
  ext x
  rw [DFA.mem_accepts, nerodeDFA_eval]
  exact nerodeClass_mem_accepting x

/-- **Every state of the Nerode automaton is reachable.** For every language $L$ and every
Nerode class $q$ of $L$, there is a word $x$ such that the Nerode automaton of $L$, started in
its start state and reading $x$, ends in the state $q$. -/
theorem nerodeDFA_state_reachable (q : NerodeClass L) :
    ∃ x, (nerodeDFA L).eval x = q := by
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨x, nerodeDFA_eval (L := L) x⟩

/-- **Finitely many Nerode classes iff finitely many left quotients.** For every language $L$,
writing $x^{-1}L = \{ y \mid xy \in L \}$ for the left quotient of $L$ by a word $x$, there are
finitely many Nerode classes of $L$ if and only if the set $\{ x^{-1}L \mid x \text{ a word} \}$
of left quotients of $L$ is finite.

This is the quotient formulation of the Myhill--Nerode criterion. -/
theorem finite_nerodeClass_iff : Finite (NerodeClass L) ↔ (Set.range L.leftQuotient).Finite := by
  constructor
  · intro h
    let _ : Finite (NerodeClass L) := h
    let _ : Finite (Set.range L.leftQuotient) :=
      Finite.of_equiv (NerodeClass L) (nerodeClassEquivResidual L)
    exact Set.toFinite _
  · intro h
    let _ := @Fintype.ofFinite (Set.range L.leftQuotient) h
    exact Finite.of_injective (nerodeClassEquivResidual L) (nerodeClassEquivResidual L).injective

/-- **Myhill–Nerode theorem, quotient form.** A language $L$ is regular, that is, accepted by some
deterministic finite automaton, if and only if $L$ has finitely many Nerode classes. -/
theorem isRegular_iff_finite_nerodeClass : L.IsRegular ↔ Finite (NerodeClass L) := by
  rw [Language.isRegular_iff_finite_range_leftQuotient, finite_nerodeClass_iff]

end Cslib.Language
