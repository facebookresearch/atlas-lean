/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.ToRecursive
public import CSLibExtTest.Computability.Machines.Turing.SingleTape.ClassesTests
public meta import CSLibExt.Computability.Machines.Turing.SingleTape.ToRecursive
public meta import Mathlib.Data.Fintype.Defs

@[expose] public section

/-!
# Tests for single-tape machines being recursive

The bridge theorems applied to the small machines of `ClassesTests` and to deciders whose input
bits are written through an injective `ι` other than the identity, and the coded step run on a
machine that writes, moves both ways and halts.
-/

set_option autoImplicit false

open Relation Computability Cslib.Turing Cslib.Decidability

namespace CSLibExtTest.Computability.Machines.Turing.SingleTape

/-! ### The bridge on small machines -/

/-- The always-true predicate on `Unit`, decided by `writeTrue`, is computable. -/
example : ComputablePred fun _ : Unit ↦ True :=
  SingleTapeDecidable.computablePred
    ⟨Bool, inferInstance, inferInstance, id, Function.injective_id, writeTrue, fun _ ↦
      ⟨true, ReflTransGen.single rfl, by simp⟩⟩

/-- With the input bits written as `ι := not`, `writeTrue` answers `[not false]` on `Unit`: it
decides the empty predicate, which is computable. -/
example : ComputablePred fun _ : Unit ↦ False :=
  SingleTapeDecidable.computablePred
    ⟨Bool, inferInstance, inferInstance, not, Bool.involutive_not.injective, writeTrue, fun _ ↦
      ⟨false, ReflTransGen.single rfl, by simp⟩⟩

/-- Write the symbol `2` and halt, on the alphabet `Fin 3`. -/
def writeTwo : SingleTapeTM (Fin 3) where
  State := Unit
  q₀ := ()
  tr _ _ := (⟨some 2, none⟩, none)

/-- On the alphabet `Fin 3` with the input bits written as `1` and `2`, `writeTwo` answers
`[2]`, the code of `true`, on `Unit`: the always-true predicate is computable. -/
example : ComputablePred fun _ : Unit ↦ True :=
  SingleTapeDecidable.computablePred
    ⟨Fin 3, inferInstance, inferInstance, fun b ↦ if b then 2 else 1, by decide, writeTwo,
      fun _ ↦ ⟨true, ReflTransGen.single rfl, by simp⟩⟩

/-- The always-true predicate, recognized by `haltNow`, is r.e. -/
example : REPred fun _ : ℕ ↦ True :=
  SingleTapeRecognizable.rePred ⟨Bool, inferInstance, inferInstance, id, Function.injective_id,
    haltNow, fun _ ↦ iff_of_true (haltNow_haltsOn _) trivial⟩

/-- The empty predicate, recognized by `loopForever`, is r.e. -/
example : REPred fun _ : ℕ ↦ False :=
  SingleTapeRecognizable.rePred ⟨Bool, inferInstance, inferInstance, id, Function.injective_id,
    loopForever, fun _ ↦ iff_of_false (not_loopForever_haltsOn _) id⟩

/-- Halting sets are r.e. on input words and on binary codes. -/
example : REPred haltNow.HaltsOn ∧ REPred fun n : ℕ ↦ loopForever.HaltsOn ((encodeNat n).map id) :=
  ⟨haltNow.rePred_haltsOn, loopForever.rePred_haltsOn_encodeNat id⟩

/-- An output is the evaluation of the step function. -/
example : writeTrue.haltCfg [true] ∈ StateTransition.eval writeTrue.step (writeTrue.initCfg []) :=
  writeTrue.outputs_iff_mem_eval.mp (ReflTransGen.single rfl)

/-- A machine that never halts has an undefined evaluation. -/
example : ¬(StateTransition.eval loopForever.step (loopForever.initCfg [true])).Dom :=
  fun h ↦ not_loopForever_haltsOn _ (loopForever.haltsOn_iff_dom_eval.mpr h)

/-! ### The coded step along a run -/

/-- In state `0`, blank the cell and move right; in state `1`, write `true` and move left; in
state `2`, write `false` and halt. -/
def zigzag : SingleTapeTM Bool where
  State := Fin 3
  q₀ := 0
  tr q _ :=
    if q = 0 then (⟨none, some .right⟩, some 1)
    else if q = 1 then (⟨some true, some .left⟩, some 2)
    else (⟨some false, none⟩, none)

/-- States of `zigzag` have decidable equality, so its codes can be compared. -/
instance : DecidableEq zigzag.State := inferInstanceAs (DecidableEq (Fin 3))

/-- The coded run of `zigzag` on `[true, false]`: the codes of the configurations, then `none`
once the halted configuration has no successor. -/
def zigzagCodedRun : List (Option zigzag.CodedCfg) :=
  (List.range 5).map fun k ↦
    (fun o ↦ o.bind zigzag.codedStep)^[k] (some (zigzag.initCfg [true, false]).toCodedCfg)

-- Blanking the first cell and moving right drops the blank (the left tape stays empty); writing
-- `true` and moving left pushes it onto the right tape; the halted code has no successor.
#guard zigzagCodedRun ==
  [some (some (0 : Fin 3), some true, [], [some false]),
    some (some (1 : Fin 3), some false, [], []), some (some (2 : Fin 3), none, [], [some true]),
    some (none, some false, [], [some true]), none]

-- A blank pushed onto a nonempty tape is kept.
#guard SingleTapeTM.codedCons none [some true] == [none, some true]

/-- `zigzag` outputs `[false, true]` on `[true, false]`. -/
theorem zigzag_outputs : zigzag.Outputs [true, false] [false, true] :=
  ReflTransGen.head rfl (ReflTransGen.head rfl (ReflTransGen.single rfl))

/-- The evaluation of `zigzag` on `[true, false]` is its output configuration. -/
example : StateTransition.eval zigzag.step (zigzag.initCfg [true, false]) =
    Part.some (zigzag.haltCfg [false, true]) :=
  Part.eq_some_iff.mpr (zigzag.outputs_iff_mem_eval.mp zigzag_outputs)

end CSLibExtTest.Computability.Machines.Turing.SingleTape
