/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.TwoWayNA.TwoWayDFA
public import Mathlib.Computability.DFA

@[expose] public section

/-!
# Tests for deterministic two-way automata

* The always-right rendering of a DFA accepts the DFA's language, checked on the
  even-length-word DFA over `Bool`.
* A deterministic two-way automaton's transition relation is functional.
* Axiom audit for the new API.
-/

set_option autoImplicit false

open Cslib.Automata

namespace Cslib.Automata.TwoWayDFA.Tests

/-- The DFA accepting the even-length words over `Bool`. -/
def evenDFA : DFA Bool (Fin 2) where
  step q _ := q + 1
  start := 0
  accept := {0}

example : [] ∈ (TwoWayDFA.ofDFA evenDFA).language := by
  rw [TwoWayDFA.language_ofDFA]
  exact (DFA.mem_accepts evenDFA).mpr rfl

example : [true] ∉ (TwoWayDFA.ofDFA evenDFA).language := by
  rw [TwoWayDFA.language_ofDFA, DFA.mem_accepts]
  intro h
  simp [evenDFA] at h

example : [true, true] ∈ (TwoWayDFA.ofDFA evenDFA).language := by
  rw [TwoWayDFA.language_ofDFA]
  refine (DFA.mem_accepts evenDFA).mpr ?_
  change (0 : Fin 2) ∈ ({0} : Set (Fin 2))
  exact Set.mem_singleton 0

/-- The transition relation of a deterministic two-way automaton is functional. -/
example {State Symbol : Type*} {A : TwoWayDFA State Symbol} {q : State} {x : Symbol}
    {m m' : SignType} {q' q'' : State} (h₁ : A.toTwoWayNA.Tr q x m q')
    (h₂ : A.toTwoWayNA.Tr q x m' q'') : (m, q') = (m', q'') :=
  A.tr_functional h₁ h₂

#print axioms Cslib.Automata.TwoWayDFA.language_isRegular
#print axioms Cslib.Automata.TwoWayDFA.language_ofDFA
#print axioms Cslib.Automata.TwoWayDFA.exists_ofDFA_of_isRegular
#print axioms Cslib.Automata.TwoWayNA.language_isRegular
#print axioms Cslib.Automata.exists_twoWayNA_of_isRegular

end Cslib.Automata.TwoWayDFA.Tests
