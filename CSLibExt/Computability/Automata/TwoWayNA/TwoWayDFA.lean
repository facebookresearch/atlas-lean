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

/-- A deterministic two-way automaton: at most one successor state and head move per
state and input symbol. -/
structure TwoWayDFA (State Symbol : Type*) where
  /-- The deterministic transition function: `step q a` is the successor state and head
  move when reading `a` in state `q`, or `none` when the run gets stuck. -/
  step : State → Symbol → Option (State × SignType)
  /-- The single start state. -/
  start : State
  /-- The set of accepting states. -/
  accept : Set State

namespace TwoWayDFA

/-- A deterministic two-way automaton as a nondeterministic two-way automaton. -/
def toTwoWayNA (A : TwoWayDFA State Symbol) : TwoWayNA State Symbol where
  Tr q x m q' := A.step q x = some (q', m)
  start := {A.start}
  accept := A.accept

/-- The transition relation of the nondeterministic rendering is the step function. -/
theorem tr_iff {A : TwoWayDFA State Symbol} {q : State} {x : Symbol} {m : SignType}
    {q' : State} : A.toTwoWayNA.Tr q x m q' ↔ A.step q x = some (q', m) :=
  Iff.rfl

/-- **Determinism**: the transition relation of a deterministic two-way automaton is
functional. -/
theorem tr_functional {A : TwoWayDFA State Symbol} {q : State} {x : Symbol} {m m' : SignType}
    {q' q'' : State} (h₁ : A.toTwoWayNA.Tr q x m q') (h₂ : A.toTwoWayNA.Tr q x m' q'') :
    (m, q') = (m', q'') := by
  change A.step q x = some (q', m) at h₁
  change A.step q x = some (q'', m') at h₂
  have h : (q'', m') = (q', m) := Option.some.inj (h₂.symm.trans h₁)
  exact Prod.ext (congrArg Prod.snd h).symm (congrArg Prod.fst h).symm

/-- The language accepted by a deterministic two-way automaton, via its nondeterministic
rendering. -/
def language (A : TwoWayDFA State Symbol) : Language Symbol :=
  Acceptor.language A.toTwoWayNA

/-- Membership in the language of a deterministic two-way automaton is acceptance by its
nondeterministic rendering. -/
theorem mem_language (A : TwoWayDFA State Symbol) (xs : List Symbol) :
    xs ∈ A.language ↔ Acceptor.Accepts A.toTwoWayNA xs :=
  Iff.rfl

/-- A deterministic two-way automaton over finitely many states accepts a regular
language. The state type is in `Type`, matching Mathlib's `Language.IsRegular`, which
quantifies over state types in `Type`. -/
theorem language_isRegular {State : Type} [Finite State] (A : TwoWayDFA State Symbol) :
    A.language.IsRegular :=
  Cslib.Language.IsRegular.iff_twoWayNA.2 ⟨State, inferInstance, A.toTwoWayNA, rfl⟩

/-- The deterministic two-way automaton simulating a DFA, always moving its head one
symbol to the right. -/
def ofDFA (M : DFA Symbol State) : TwoWayDFA State Symbol where
  step q a := some (M.step q a, SignType.pos)
  start := M.start
  accept := M.accept

/-- The nondeterministic rendering of the DFA simulation is the two-way rendering of
the NFA obtained from the DFA. -/
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

/-- A DFA and its always-right deterministic two-way rendering accept the same
language. -/
theorem language_ofDFA (M : DFA Symbol State) :
    (TwoWayDFA.ofDFA M).language = M.accepts := by
  unfold language
  rw [toTwoWayNA_ofDFA, TwoWayNA.language_toTwoWayNA,
    DA.FinAcc.toNAFinAcc_language_eq, DA.FinAcc.accepts_ofDFA]

/-- Every regular language is accepted by a deterministic two-way automaton. -/
theorem exists_ofDFA_of_isRegular {L : Language Symbol} (hL : L.IsRegular) :
    ∃ (S : Type) (_ : Fintype S) (A : TwoWayDFA S Symbol), A.language = L := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  exact ⟨σ, inferInstance, TwoWayDFA.ofDFA M, TwoWayDFA.language_ofDFA M⟩

end TwoWayDFA

/-- Every upstream nondeterministic two-way automaton over finitely many states accepts
a regular language. The state type is in `Type`, matching Mathlib's `Language.IsRegular`. -/
theorem TwoWayNA.language_isRegular {State : Type} [Finite State] (a : TwoWayNA State Symbol) :
    (Acceptor.language a).IsRegular :=
  Cslib.Language.IsRegular.iff_twoWayNA.2 ⟨State, inferInstance, a, rfl⟩

/-- Every regular language is accepted by an upstream nondeterministic two-way
automaton. -/
theorem exists_twoWayNA_of_isRegular {L : Language Symbol} (hL : L.IsRegular) :
    ∃ (S : Type) (_ : Finite S) (a : TwoWayNA S Symbol),
      Acceptor.language a = L :=
  Cslib.Language.IsRegular.iff_twoWayNA.1 hL

end Cslib.Automata
