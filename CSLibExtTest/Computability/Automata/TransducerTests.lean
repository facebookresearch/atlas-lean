/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.Transducers.Sequential
public import Cslib.Computability.Languages.RegularLanguage
public import Mathlib.Computability.Language

@[expose] public section

/-!
# Tests for sequential transducers, Mealy machines, and Moore machines

* The identity Mealy machine translates `[true, false]` to itself.
* A Moore machine outputting its current state translates `[true, false]` to
  `[false, true, false]`.
* Composing the identity sequential transducer with itself translates `[true]` to
  `[true]`.
* The preimage of the empty-word language under the identity transducer is regular.
* Axiom audit for the new API.
-/

set_option autoImplicit false

open Cslib.Automata

namespace Cslib.Automata.Transducer.Tests

/-- The identity Mealy machine over `Bool`. -/
def idMealy : MealyMachine Unit Bool Bool where
  step _ a := ((), a)
  start := ()

/-- A Moore machine outputting its current state, starting in `false`. -/
def stateMoore : MooreMachine Bool Bool Bool where
  step _ a := a
  out q := q
  start := false

/-- The identity sequential transducer over `Bool`. -/
def idSeq : SequentialTransducer Unit Bool Bool where
  step _ a := ((), [a])
  start := ()
  accept := Set.univ
  initOut := []
  finalOut := fun _ => []

example : (idMealy.toSequential).Translates [true, false] [true, false] := by
  rw [MealyMachine.translates_toSequential_iff]
  rfl

example : ¬ (idMealy.toSequential).Translates [true] [false] := by
  rw [MealyMachine.translates_toSequential_iff]
  intro h
  change [true] = [false] at h
  exact absurd h (by decide)

example : (stateMoore.toSequential).Translates [true, false] [false, true, false] := by
  rw [MooreMachine.translates_toSequential_iff]
  rfl

example : (SequentialTransducer.comp idSeq idSeq).Translates [true] [true] := by
  rw [SequentialTransducer.translates_comp_iff]
  refine ⟨[true], ?_, ?_⟩ <;> refine ⟨?_, ?_⟩ <;> first | exact Set.mem_univ _ | rfl

example : (SequentialTransducer.preimage idSeq (1 : Language Bool)).IsRegular :=
  SequentialTransducer.isRegular_preimage idSeq Cslib.Language.IsRegular.one

#print axioms Cslib.Automata.SequentialTransducer.translates_comp_iff
#print axioms Cslib.Automata.SequentialTransducer.isRegular_preimage
#print axioms Cslib.Automata.MealyMachine.translates_toSequential_iff
#print axioms Cslib.Automata.MooreMachine.translates_toSequential_iff

end Cslib.Automata.Transducer.Tests
