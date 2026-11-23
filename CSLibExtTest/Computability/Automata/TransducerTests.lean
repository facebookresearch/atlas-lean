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

universe u v w

example {State : Type u} {In Out : Type v}
    (S : SequentialTransducer State In Out) (xs : List In) (ys : List Out) :
    Transducer.Translates S xs ys ↔ S.Translates xs ys :=
  SequentialTransducer.translates_iff S xs ys

example {State : Type u} {In : Type v} {Out : Type w}
    (S : SequentialTransducer State In Out) :
    S.Translates [] (S.initOut ++ S.finalOut S.start) ↔ S.start ∈ S.accept := by
  simp only [SequentialTransducer.Translates, SequentialTransducer.runState_nil,
    SequentialTransducer.runOut_nil, List.append_nil, and_true]

/-- A sequential transducer erasing its input and emitting initial and final markers. -/
def framedSeq : SequentialTransducer Unit Bool Bool where
  step _ _ := ((), [])
  start := ()
  accept := Set.univ
  initOut := [true]
  finalOut _ := [false]

example : Transducer.Translates framedSeq [] [true, false] :=
  ⟨Set.mem_univ _, rfl⟩

example : Transducer.Translates framedSeq [false] [true, false] :=
  ⟨Set.mem_univ _, rfl⟩

example : ¬ Transducer.Translates
    (show SequentialTransducer Unit Bool Bool from { idSeq with accept := ∅ }) [] [] := by
  rintro ⟨h, _⟩
  exact h

example : Transducer.Translates idSeq [] [] :=
  ⟨Set.mem_univ _, rfl⟩

example : Transducer.Translates idMealy [true, false] [true, false] := by
  rw [MealyMachine.translates_iff]
  rfl

example : ¬ Transducer.Translates idMealy [true] [false] := by
  rw [MealyMachine.translates_iff]
  decide

example : Transducer.Translates stateMoore [] [false] := by
  rw [MooreMachine.translates_iff]
  rfl

example : ¬ Transducer.Translates stateMoore [] [] := by
  rw [MooreMachine.translates_iff]
  decide

example {State : Type u} {In Out : Type v} (M : MealyMachine State In Out)
    (xs : List In) (ys : List Out) :
    Transducer.Translates M xs ys ↔ M.transduce xs = ys :=
  MealyMachine.translates_iff M xs ys

example {State : Type u} {In Out : Type v} (M : MooreMachine State In Out)
    (xs : List In) (ys : List Out) :
    Transducer.Translates M xs ys ↔ M.transduce xs = ys :=
  MooreMachine.translates_iff M xs ys

#print axioms Cslib.Automata.SequentialTransducer.translates_iff
#print axioms Cslib.Automata.MealyMachine.translates_iff
#print axioms Cslib.Automata.MooreMachine.translates_iff

#print axioms Cslib.Automata.SequentialTransducer.translates_comp_iff
#print axioms Cslib.Automata.SequentialTransducer.isRegular_preimage
#print axioms Cslib.Automata.MealyMachine.translates_toSequential_iff
#print axioms Cslib.Automata.MooreMachine.translates_toSequential_iff

end Cslib.Automata.Transducer.Tests
