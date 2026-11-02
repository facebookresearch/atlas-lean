/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Deterministic two-way automata
-/
module

public import Cslib.Computability.Automata.TwoWayNA.Basic
public import Cslib.Computability.Automata.TwoWayNA.OfNA
public import CSLibExt.Computability.Automata.DA.MathlibDFA
public import Mathlib.Computability.DFA
public import Mathlib.Computability.Language

/-!
# Deterministic two-way automata

A deterministic two-way automaton (`TwoWayDFA`) is the deterministic special case of
upstream's nondeterministic two-way automaton (`Cslib.Automata.TwoWayNA`): its transition
function returns at most one successor state and head move, instead of a transition
relation. The head may move left (`SignType.neg`), stay (`SignType.zero`), or move right
(`SignType.pos`), matching upstream's convention. Acceptance is inherited from the
nondeterministic rendering (`TwoWayDFA.toTwoWayNA`), so a deterministic two-way
automaton is literally a two-way nondeterministic automaton with a functional transition
relation (`TwoWayDFA.tr_functional`).

## Main results

* `Cslib.Automata.TwoWayDFA.language_isRegular`: a two-way deterministic automaton over
  finitely many states accepts a regular language, via upstream's two-way-to-one-way
  reduction (`Cslib.Language.IsRegular.iff_twoWayNA`, Vardi's proof).
* `Cslib.Automata.TwoWayDFA.language_ofDFA`: a DFA and its always-right two-way rendering
  accept the same language.
* `Cslib.Automata.TwoWayDFA.exists_ofDFA_of_isRegular`: every regular language is accepted
  by a deterministic two-way automaton.
* `Cslib.Automata.TwoWayNA.language_isRegular` and
  `Cslib.Automata.exists_twoWayNA_of_isRegular`: the same equivalence for upstream's
  nondeterministic two-way automata, stated against Mathlib's `Language.IsRegular`.
  Upstream already defines `TwoWayNA` and proves the hard direction by Vardi's
  rejection-certificate construction (`TwoWayNA.complToNA`); it is not redefined here.
-/

@[expose] public section

open Cslib.Language

namespace Cslib.Automata

variable {State Symbol : Type*}

/-- **Deterministic two-way automaton.** A deterministic two-way automaton with state set $Q$
over the alphabet $\Sigma$ consists of a partial transition function, which assigns to each
state $q \in Q$ and input symbol $a \in \Sigma$ at most one pair of a successor state and a head
move (left, stay or right), together with a single start state and a set of accepting states. -/
structure TwoWayDFA (State Symbol : Type*) where
  /-- The deterministic transition function: `step q a` is the successor state and head
  move when reading `a` in state `q`, or `none` when the run gets stuck. -/
  step : State → Symbol → Option (State × SignType)
  /-- The single start state. -/
  start : State
  /-- The set of accepting states. -/
  accept : Set State

namespace TwoWayDFA

/-- **A deterministic two-way automaton as a nondeterministic one.** A deterministic two-way
automaton $A$ is viewed as the nondeterministic two-way automaton with the same states and
accepting states, whose only start state is the start state of $A$, and which can go from state
$q$ reading a symbol $a$ to state $q'$ with head move $m$ exactly when the step function of $A$
at $q$ and $a$ returns $q'$ and $m$. -/
def toTwoWayNA (A : TwoWayDFA State Symbol) : TwoWayNA State Symbol where
  Tr q x m q' := A.step q x = some (q', m)
  start := {A.start}
  accept := A.accept

/-- **Transition relation of a deterministic two-way automaton.** Let $A$ be a deterministic
two-way automaton, viewed as a nondeterministic two-way automaton. On reading the symbol $x$ in
state $q$, it has a transition to state $q'$ with head move $m$ if and only if the transition
function of $A$ sends $(q, x)$ to the pair $(q', m)$. -/
theorem tr_iff {A : TwoWayDFA State Symbol} {q : State} {x : Symbol} {m : SignType}
    {q' : State} : A.toTwoWayNA.Tr q x m q' ↔ A.step q x = some (q', m) :=
  Iff.rfl

/-- **Deterministic two-way automata have unique transitions.** Let $A$ be a deterministic
two-way automaton, viewed as a nondeterministic two-way automaton. If, on reading the symbol
$x$ in state $q$, it has a transition to state $q'$ with head move $m$ and a transition to
state $q''$ with head move $m'$, then $m = m'$ and $q' = q''$. -/
theorem tr_functional {A : TwoWayDFA State Symbol} {q : State} {x : Symbol} {m m' : SignType}
    {q' q'' : State} (h₁ : A.toTwoWayNA.Tr q x m q') (h₂ : A.toTwoWayNA.Tr q x m' q'') :
    (m, q') = (m', q'') := by
  change A.step q x = some (q', m) at h₁
  change A.step q x = some (q'', m') at h₂
  have h : (q'', m') = (q', m) := Option.some.inj (h₂.symm.trans h₁)
  exact Prod.ext (congrArg Prod.snd h).symm (congrArg Prod.fst h).symm

/-- **Language of a deterministic two-way automaton.** The language of a deterministic two-way
automaton $A$ is the set of words accepted by $A$ viewed as a nondeterministic two-way
automaton: a word $w$ belongs to it when, starting in the start state with the head at the
first position of $w$ and following the step function of $A$ (which moves the head one
position left, keeps it in place, or moves it one position right, and gets stuck when it is
undefined or would move the head left of the first position), the automaton reaches an
accepting state with the head just past the last symbol of $w$. -/
def language (A : TwoWayDFA State Symbol) : Language Symbol :=
  Acceptor.language A.toTwoWayNA

/-- **Membership in the language of a two-way deterministic automaton.** For every
deterministic two-way automaton $A$ and every word $w$, $w$ belongs to the language of $A$ if
and only if $w$ is accepted by $A$ viewed as a nondeterministic two-way automaton. -/
theorem mem_language (A : TwoWayDFA State Symbol) (xs : List Symbol) :
    xs ∈ A.language ↔ Acceptor.Accepts A.toTwoWayNA xs :=
  Iff.rfl

/-- **Finite two-way deterministic automata accept regular languages.** The language of every
deterministic two-way automaton with finitely many states is regular. -/
theorem language_isRegular {State : Type} [Finite State] (A : TwoWayDFA State Symbol) :
    A.language.IsRegular :=
  Cslib.Language.IsRegular.iff_twoWayNA.2 ⟨State, inferInstance, A.toTwoWayNA, rfl⟩

/-- **A DFA as a two-way deterministic automaton.** For a DFA $M$ with transition function
$\delta$, this is the deterministic two-way automaton with the same states, start state and
accepting states as $M$ which, in state $q$ reading a symbol $a$, goes to state $\delta(q, a)$
and moves its head one symbol to the right. -/
def ofDFA (M : DFA Symbol State) : TwoWayDFA State Symbol where
  step q a := some (M.step q a, SignType.pos)
  start := M.start
  accept := M.accept

/-- **The two-way simulation of a DFA agrees with that of its NFA.** For every DFA $M$, the
deterministic two-way automaton that simulates $M$, viewed as a nondeterministic two-way
automaton, equals the nondeterministic two-way automaton obtained by viewing $M$ as an NFA and
letting that NFA always move its head one symbol to the right. -/
theorem toTwoWayNA_ofDFA (M : DFA Symbol State) :
    (TwoWayDFA.ofDFA M).toTwoWayNA =
      (DA.FinAcc.toNAFinAcc (DA.FinAcc.ofDFA M)).toTwoWayNA := by
  change TwoWayNA.mk (fun q x m q' => some (M.step q x, SignType.pos) = some (q', m))
      {M.start} M.accept =
    TwoWayNA.mk (fun q x m q' => m = SignType.pos ∧ M.step q x = q') {M.start} M.accept
  rw [TwoWayNA.mk.injEq]
  refine ⟨?_, rfl, rfl⟩
  funext q x m q'
  apply propext
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₂.symm, h₁⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₂, h₁.symm⟩

/-- **The two-way simulation of a DFA accepts the same language.** For every DFA $M$, the
deterministic two-way automaton that simulates $M$ by always moving its head one symbol to the
right has exactly the language accepted by $M$. -/
theorem language_ofDFA (M : DFA Symbol State) :
    (TwoWayDFA.ofDFA M).language = M.accepts := by
  unfold language
  rw [toTwoWayNA_ofDFA, TwoWayNA.language_toTwoWayNA,
    DA.FinAcc.toNAFinAcc_language_eq, DA.FinAcc.accepts_ofDFA]

/-- **Regular languages are accepted by two-way deterministic automata.** For every regular
language $L$ over an alphabet, there is a deterministic two-way automaton with finitely many
states whose language is exactly $L$. -/
theorem exists_ofDFA_of_isRegular {L : Language Symbol} (hL : L.IsRegular) :
    ∃ (S : Type) (_ : Fintype S) (A : TwoWayDFA S Symbol), A.language = L := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  exact ⟨σ, inferInstance, TwoWayDFA.ofDFA M, TwoWayDFA.language_ofDFA M⟩

end TwoWayDFA

/-- **Finite two-way nondeterministic automata accept regular languages.** Every
nondeterministic two-way automaton with finitely many states accepts a regular language.

A run of such an automaton on a word starts in a start state with the head at the first
position; each step reads the symbol under the head, changes the state and moves the head one
position left, keeps it in place, or moves it one position right, and the run is stuck if the
head would move left of the first position. A word is accepted when some run ends in an
accepting state with the head just past the last symbol. -/
theorem TwoWayNA.language_isRegular {State : Type} [Finite State] (a : TwoWayNA State Symbol) :
    (Acceptor.language a).IsRegular :=
  Cslib.Language.IsRegular.iff_twoWayNA.2 ⟨State, inferInstance, a, rfl⟩

/-- **Regular languages are accepted by two-way nondeterministic automata.** For every
regular language $L$ over an alphabet, there is a nondeterministic two-way automaton with
finitely many states that accepts exactly the words of $L$.

A run of such an automaton on a word starts in a start state with the head at the first
position; each step reads the symbol under the head, changes the state and moves the head one
position left, keeps it in place, or moves it one position right, and the run is stuck if the
head would move left of the first position. A word is accepted when some run ends in an
accepting state with the head just past the last symbol. -/
theorem exists_twoWayNA_of_isRegular {L : Language Symbol} (hL : L.IsRegular) :
    ∃ (S : Type) (_ : Finite S) (a : TwoWayNA S Symbol),
      Acceptor.language a = L :=
  Cslib.Language.IsRegular.iff_twoWayNA.1 hL

end Cslib.Automata
