/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Upstream deterministic automata and Mathlib DFAs
-/
module

public import Cslib.Computability.Languages.MyhillNerode
public import CSLibExt.Computability.Languages.Congruences.Minimization

/-!
# Upstream deterministic automata and Mathlib DFAs

Upstream CSLib's finite-word deterministic automata (`Cslib.Automata.DA.FinAcc`, with its
Myhill–Nerode development in `Cslib.Computability.Languages.MyhillNerode`) and Mathlib's `DFA`
(with the syntactic-monoid and minimization development in
`CSLibExt/Computability/Languages/Congruences/`) are parallel. This file identifies them.

* `Cslib.Automata.DA.FinAcc.toDFA` and `Cslib.Automata.DA.FinAcc.ofDFA`: the two kinds of
  automata are the same data (mutually inverse, `toDFA_ofDFA`, `ofDFA_toDFA`), and they accept the
  same language (`language_toDFA`, `accepts_ofDFA`).
* `Cslib.Automata.DA.FinAcc.nerodeCongruence_r_iff`: the upstream Nerode congruence is
  `Cslib.Language.nerodeRel`.
* `Cslib.Automata.DA.FinAcc.reindex_nerodeCongruenceDA`: the upstream canonical minimal automaton
  `l.NerodeCongruenceDA`, with its classes renamed to the residual languages they determine, is
  exactly Mathlib's `Language.toDFA l`.
* `Cslib.Automata.DA.FinAcc.reindex_nerodeCongruenceDA_eq_minimizedDFA`: hence it is also
  `Cslib.Language.minimizedDFA M` for any DFA `M` with that language.
-/

@[expose] public section

namespace Cslib.Automata.DA.FinAcc

open Cslib.Language

/-! ## The two kinds of automata -/

section Conversions

variable {State Symbol : Type*}

/-- **CSLib automata as Mathlib DFAs.** A CSLib deterministic automaton $M$ on finite words is
viewed as a Mathlib DFA with the same states, the same transition function, the same start state
and the same set of accepting states as $M$. -/
def toDFA (M : DA.FinAcc State Symbol) : DFA Symbol State where
  step := M.tr
  start := M.start
  accept := M.accept

/-- **Mathlib DFAs as CSLib automata.** A Mathlib DFA $M$ is viewed as a CSLib deterministic
automaton on finite words with the same states, the same transition function, the same start state
and the same set of accepting states as $M$. -/
def ofDFA (M : DFA Symbol State) : DA.FinAcc State Symbol where
  tr := M.step
  start := M.start
  accept := M.accept

@[simp]
theorem toDFA_ofDFA (M : DFA Symbol State) : toDFA (ofDFA M) = M :=
  rfl

@[simp]
theorem ofDFA_toDFA (M : DA.FinAcc State Symbol) : ofDFA (toDFA M) = M :=
  rfl

theorem toDFA_evalFrom (M : DA.FinAcc State Symbol) (s : State) (xs : List Symbol) :
    M.toDFA.evalFrom s xs = M.mtr s xs :=
  rfl

/-- **Converting a CSLib automaton to a Mathlib DFA preserves its language.** For every
deterministic automaton $M$ on finite words, the DFA with the same states, transition function,
start state and accepting states as $M$ accepts exactly the language of $M$. -/
@[simp]
theorem language_toDFA (M : DA.FinAcc State Symbol) :
    M.toDFA.accepts = Acceptor.language M :=
  rfl

@[simp]
theorem accepts_ofDFA (M : DFA Symbol State) : Acceptor.language (ofDFA M) = M.accepts :=
  rfl

end Conversions

/-! ## The Nerode congruence and the canonical automata -/

section Nerode

variable {Symbol : Type} {l : Language Symbol}

/-- **The Nerode congruence relates words with equal left quotients.** Let $L$ be a language
over an alphabet $\Sigma$ and let $x, y \in \Sigma^*$. Then $x$ and $y$ are related by the Nerode
congruence of $L$, that is, $xz \in L \iff yz \in L$ for every word $z$, if and only if they are
Nerode equivalent for $L$, that is, their left quotients $x^{-1}L = \{z : xz \in L\}$ and
$y^{-1}L$ are equal. -/
theorem nerodeCongruence_r_iff {x y : List Symbol} :
    l.NerodeCongruence.r x y ↔ nerodeRel l x y := by
  change (∀ z, x ++ z ∈ l ↔ y ++ z ∈ l) ↔ l.leftQuotient x = l.leftQuotient y
  constructor
  · intro h
    ext z
    exact h z
  · intro h z
    change z ∈ l.leftQuotient x ↔ z ∈ l.leftQuotient y
    rw [h]

/-- **The residual language of a Nerode class.** Let $L$ be a language over an alphabet
$\Sigma$, and write $x^{-1}L = \{z : xz \in L\}$ for the left quotient of $L$ by a word $x$. This
is the map from the classes of the Nerode congruence of $L$ to the set
$\{w^{-1}L : w \in \Sigma^*\}$ of residual languages of $L$ that sends the class of each word $x$
to $x^{-1}L$; it is well defined because Nerode-congruent words have the same left quotient. -/
def nerodeResidual (l : Language Symbol) : l.NerodeQuotient → Set.range l.leftQuotient :=
  Quotient.lift (fun x => ⟨l.leftQuotient x, x, rfl⟩)
    (fun _ _ h => Subtype.ext (nerodeCongruence_r_iff.1 h))

theorem nerodeResidual_mk (x : List Symbol) :
    nerodeResidual l ⟦x⟧ = ⟨l.leftQuotient x, x, rfl⟩ :=
  rfl

theorem nerodeResidual_bijective : Function.Bijective (nerodeResidual l) := by
  constructor
  · intro p q h
    induction p using Quotient.inductionOn
    induction q using Quotient.inductionOn
    exact Quotient.sound (nerodeCongruence_r_iff.2 (congrArg Subtype.val h))
  · rintro ⟨L, x, rfl⟩
    exact ⟨⟦x⟧, rfl⟩

/-- **Nerode classes are the residual languages.** Let $L$ be a language over an alphabet
$\Sigma$, and write $x^{-1}L = \{z : xz \in L\}$ for the left quotient of $L$ by a word $x$. This
is the bijection from the classes of the Nerode congruence of $L$ onto the set
$\{x^{-1}L : x \in \Sigma^*\}$ of residual languages of $L$ that sends the class of each word $x$
to $x^{-1}L$.

The residual languages are the states of Mathlib's residual-language DFA of $L$. -/
noncomputable def nerodeQuotientEquivResidual (l : Language Symbol) :
    l.NerodeQuotient ≃ Set.range l.leftQuotient :=
  Equiv.ofBijective _ nerodeResidual_bijective

private theorem dfa_ext {α τ : Type*} {A B : DFA α τ} (h₁ : A.step = B.step)
    (h₂ : A.start = B.start) (h₃ : A.accept = B.accept) : A = B := by
  cases A
  cases B
  cases h₁
  cases h₂
  cases h₃
  rfl

/-- **The Nerode automaton is the residual-language automaton.** Let $L$ be a language over an
alphabet $\Sigma$, and write $x^{-1}L = \{z : xz \in L\}$ for the left quotient of $L$ by a word
$x$. Consider the canonical automaton of $L$ as a DFA: its states are the classes $[x]$ of the
Nerode congruence of $L$, its start state is the class of the empty word, on a letter $a$ it goes
from $[x]$ to $[xa]$, and its accepting states are the classes of words of $L$. Renaming each
class $[x]$ to $x^{-1}L$ gives exactly Mathlib's residual-language DFA of $L$: its states are the
residual languages $x^{-1}L$ for $x \in \Sigma^*$, its start state is $L$, on a letter $a$ it goes
from $K$ to $a^{-1}K$, and its accepting states are the residual languages that contain the empty
word. -/
theorem reindex_nerodeCongruenceDA (l : Language Symbol) :
    DFA.reindex (nerodeQuotientEquivResidual l) (toDFA l.NerodeCongruenceDA) = l.toDFA := by
  have hsurj : ∀ q : Set.range l.leftQuotient, ∃ x : List Symbol,
      nerodeQuotientEquivResidual l ⟦x⟧ = q := by
    rintro ⟨L, x, rfl⟩
    exact ⟨x, rfl⟩
  refine dfa_ext ?_ ?_ ?_
  · funext q a
    obtain ⟨x, rfl⟩ := hsurj q
    apply Subtype.ext
    change (nerodeQuotientEquivResidual l ((toDFA l.NerodeCongruenceDA).step
      ((nerodeQuotientEquivResidual l).symm (nerodeQuotientEquivResidual l ⟦x⟧)) a)).val = _
    rw [Equiv.symm_apply_apply]
    change l.leftQuotient (x ++ [a]) = (l.leftQuotient x).leftQuotient [a]
    exact Language.leftQuotient_append l x [a]
  · rfl
  · ext q
    obtain ⟨x, rfl⟩ := hsurj q
    change (nerodeQuotientEquivResidual l).symm (nerodeQuotientEquivResidual l ⟦x⟧) ∈
        (Quotient.mk _ '' l : Set l.NerodeQuotient) ↔ [] ∈ l.leftQuotient x
    rw [Equiv.symm_apply_apply, Language.mem_leftQuotient, List.append_nil]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have h := (Quotient.exact hyx) []
      simp only [List.append_nil] at h
      exact h.1 hy
    · intro hx
      exact ⟨x, hx, rfl⟩

/-- **The canonical automaton of a DFA's language is its minimized DFA.** Let $M$ be a DFA over
an alphabet $\Sigma$ accepting the language $L$, and write $x^{-1}L = \{z : xz \in L\}$ for the
left quotient of $L$ by a word $x$. Consider the canonical automaton of $L$ as a DFA: its states
are the classes $[x]$ of the Nerode congruence of $L$, its start state is the class of the empty
word, on a letter $a$ it goes from $[x]$ to $[xa]$, and its accepting states are the classes of
words of $L$. Renaming each class $[x]$ to $x^{-1}L$, regarded as one of the languages accepted
from the states of $M$ reachable from its start state, gives exactly the minimized DFA of $M$. -/
theorem reindex_nerodeCongruenceDA_eq_minimizedDFA {State : Type*} (M : DFA Symbol State) :
    DFA.reindex ((nerodeQuotientEquivResidual M.accepts).trans
      (leftQuotientEquivReachableResiduals M)) (toDFA M.accepts.NerodeCongruenceDA) =
        minimizedDFA M := by
  rw [minimizedDFA, ← reindex_nerodeCongruenceDA]
  rfl

end Nerode

end Cslib.Automata.DA.FinAcc
