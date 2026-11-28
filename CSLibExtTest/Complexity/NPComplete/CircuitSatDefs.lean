/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CircuitSatDefs

namespace MetaMathlibExt.Complexity.NPComplete.CircuitSat

/-- `NOT x₀`: gate `0` reads variable `0`, gate `1` negates input `1`, which is gate `0`. -/
private abbrev notX : CircuitSatInstance := (1, [(3, 0, 0), (2, 1, 0)])

/-- `x₀ AND NOT x₀`: gate `2` conjoins inputs `1` and `2`, which are gates `0` and `1`. -/
private abbrev xAndNotX : CircuitSatInstance := (1, [(3, 0, 0), (2, 1, 0), (0, 1, 2)])

/-- Every assignment to one variable is a singleton list. -/
private theorem eq_singleton {a : List Bool} (h : a.length = 1) : ∃ b, a = [b] :=
  List.length_eq_one_iff.mp h

/-- Evaluation keeps one value per gate, in order. -/
example : EvalCircuit [true] notX.2 = [true, false] := by decide

example : EvalCircuit [false] xAndNotX.2 = [false, true, false] := by decide

private theorem notX_wellFormed : WellFormed notX := by unfold WellFormed; decide

private theorem contradiction_wellFormed : WellFormed xAndNotX := by
  unfold WellFormed; decide

/-- `x₀ = false` satisfies `NOT x₀`. -/
private theorem notX_feasible : CircuitSatFeasible notX := ⟨[false], rfl, by decide⟩

/-- No assignment satisfies `x₀ AND NOT x₀`. -/
private theorem contradiction_infeasible : ¬ CircuitSatFeasible xAndNotX := by
  rintro ⟨a, ha, h⟩
  obtain ⟨b, rfl⟩ := eq_singleton ha
  cases b <;> revert h <;> decide

/-- The assignment must have exactly one entry per variable. -/
example : ¬ ([false, false].length = notX.1) := by decide

/-- The output is the last gate: a true earlier gate does not help. -/
example : ¬ CircuitSatFeasible ((0, [(4, 0, 0), (5, 0, 0)]) : CircuitSatInstance) := by
  rintro ⟨a, ha, h⟩
  obtain rfl : a = [] := List.length_eq_zero_iff.mp ha
  revert h; decide

/-- The empty circuit is well formed but has no output, so it is not satisfiable. -/
example : WellFormed ((0, []) : CircuitSatInstance) := by unfold WellFormed; decide

example : ¬ CircuitSatFeasible ((0, []) : CircuitSatInstance) := by
  rintro ⟨a, -, h⟩
  simp [EvalCircuit] at h

/-- Unused inputs are unconstrained: the second input of a `NOT` gate and both inputs of a
constant gate may be arbitrary. -/
example : WellFormed ((1, [(3, 0, 0), (2, 1, 99), (4, 7, 9)]) : CircuitSatInstance) := by
  unfold WellFormed; decide

/-- A gate may read itself only through a malformed reference: `x₀ OR g₀` is satisfiable
(the self-reference evaluates to false) but malformed. -/
private abbrev selfRef : CircuitSatInstance := (1, [(1, 0, 1)])

private theorem selfRef_feasible : CircuitSatFeasible selfRef := ⟨[true], rfl, by decide⟩

private theorem selfRef_malformed : ¬ WellFormed selfRef := by unfold WellFormed; decide

/-- A `NOT` gate reading a missing input is satisfiable (the input reads as false) but
malformed. -/
private abbrev danglingNot : CircuitSatInstance := (0, [(2, 5, 0)])

private theorem danglingNot_feasible : CircuitSatFeasible danglingNot := ⟨[], rfl, by decide⟩

private theorem danglingNot_malformed : ¬ WellFormed danglingNot := by unfold WellFormed; decide

/-- Malformed: an operation code above `5`, and a variable gate out of range. -/
example : ¬ WellFormed ((1, [(6, 0, 0)]) : CircuitSatInstance) := by unfold WellFormed; decide

example : ¬ WellFormed ((1, [(3, 1, 0)]) : CircuitSatInstance) := by unfold WellFormed; decide

open MetaMathlibExt.BitstringEncoding

/-- The decision problem accepts `NOT x₀`. -/
example : circuitSatDec (bitEncode notX) = true := by
  simp [circuitSatDec, notX_wellFormed, notX_feasible]

/-- It rejects the well-formed xAndNotX. -/
example : circuitSatDec (bitEncode xAndNotX) = false := by
  simp [circuitSatDec, contradiction_infeasible]

/-- It rejects the satisfiable malformed circuits. -/
example :
    circuitSatDec (bitEncode selfRef) = false ∧ circuitSatDec (bitEncode danglingNot) = false := by
  simp [circuitSatDec, selfRef_malformed, danglingNot_malformed]

example : CircuitSatFeasible selfRef ∧ CircuitSatFeasible danglingNot :=
  ⟨selfRef_feasible, danglingNot_feasible⟩

/-- It rejects the empty bitstring, which decodes to no instance. -/
example : circuitSatDec [] = false := by
  have h : bitDecode (α := CircuitSatInstance) [] = none := rfl
  simp [circuitSatDec, h]

end MetaMathlibExt.Complexity.NPComplete.CircuitSat
