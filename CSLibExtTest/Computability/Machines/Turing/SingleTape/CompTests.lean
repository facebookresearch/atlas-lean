/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.Comp
public import CSLibExtTest.Computability.Machines.Turing.SingleTape.ClassesTests

@[expose] public section

/-!
# Tests for composed single-tape machines

`compComputer` on the small machines of `ClassesTests`: outputs and time bounds compose, and a
composite halts exactly when its second machine halts on the first machine's output.
-/

set_option autoImplicit false

open Relation Cslib.Turing

namespace CSLibExtTest.Computability.Machines.Turing.SingleTape

/-- `haltNow` outputs its input, in one step. -/
theorem haltNow_outputsWithinTime (l : List Bool) : haltNow.OutputsWithinTime l l 1 :=
  RelatesWithinSteps.single rfl

/-- `writeTrue` outputs `[true]` on the empty input, in one step. -/
theorem writeTrue_outputsWithinTime : writeTrue.OutputsWithinTime [] [true] 1 :=
  RelatesWithinSteps.single rfl

/-- A two-step machine that outputs its input: rewrite the head cell, then rewrite it again and
halt. -/
def stepTwice : SingleTapeTM Bool where
  State := Bool
  q₀ := false
  tr q s := (⟨s, none⟩, if q then none else some true)

/-- `stepTwice` outputs its input in two steps. -/
theorem stepTwice_outputsWithinTime (l : List Bool) : stepTwice.OutputsWithinTime l l 2 :=
  RelatesWithinSteps.of_relatesInSteps (RelatesInSteps.head _ _ _ _ rfl (RelatesInSteps.single rfl))

/-- A first machine that runs two steps: the composite takes three. -/
example : (SingleTapeTM.compComputer stepTwice writeTrue).OutputsWithinTime [] [true] 3 :=
  (stepTwice_outputsWithinTime []).compComputer writeTrue_outputsWithinTime

/-- Outputs compose, and the step counts add. -/
example : (SingleTapeTM.compComputer haltNow writeTrue).OutputsWithinTime [] [true] 2 :=
  (haltNow_outputsWithinTime []).compComputer writeTrue_outputsWithinTime

example : (SingleTapeTM.compComputer haltNow writeTrue).Outputs [] [true] :=
  let ⟨_, _, h₁⟩ := haltNow_outputsWithinTime []
  let ⟨_, _, h₂⟩ := writeTrue_outputsWithinTime
  SingleTapeTM.Outputs.compComputer h₁.reflTransGen h₂.reflTransGen

/-- A composite whose second machine never halts never halts. -/
example (l : List Bool) : ¬(SingleTapeTM.compComputer haltNow loopForever).HaltsOn l := by
  let ⟨_, _, h⟩ := haltNow_outputsWithinTime l
  rw [SingleTapeTM.haltsOn_compComputer_iff h.reflTransGen]
  exact not_loopForever_haltsOn l

/-- A composite whose second machine halts at once halts. -/
example (l : List Bool) : (SingleTapeTM.compComputer haltNow haltNow).HaltsOn l := by
  let ⟨_, _, h⟩ := haltNow_outputsWithinTime l
  rw [SingleTapeTM.haltsOn_compComputer_iff h.reflTransGen]
  exact haltNow_haltsOn l

end CSLibExtTest.Computability.Machines.Turing.SingleTape
