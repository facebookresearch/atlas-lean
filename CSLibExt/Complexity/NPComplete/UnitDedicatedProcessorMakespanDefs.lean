/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIT-TIME DEDICATED-PROCESSOR SCHEDULING, MAKESPAN (P|fixⱼ, pⱼ = 1|C_max): definitions

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272,
doi:10.1016/0166-218X(94)90012-4, Theorem 2.5 (deciding whether an instance of
`P|fixⱼ, pⱼ = 1|C_max` has a schedule of length at most 3 is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Multiprocessor task problems with
dedicated processors", which lists the problem as minimal NP-hard with this attribution.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitDedicatedProcessorMakespan

/-- An instance: the number `m` of processors, the processor sets `fixⱼ` of the tasks, and the
bound `K`. -/
abbrev UnitDedicatedProcessorInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: there is at least one processor (`0 < m`); every task has a
nonempty set of processors, listed without repetitions, all below `m`; and `0 < K`. -/
def WellFormed (i : UnitDedicatedProcessorInstance) : Prop :=
  0 < i.1 ∧ (∀ f ∈ i.2.1, f ≠ [] ∧ f.Nodup ∧ ∀ k ∈ f, k < i.1) ∧ 0 < i.2.2

/-- There are start times `s` with makespan at most `K` (every `s j + 1 ≤ K`) such that any two
different tasks with a common processor are processed in disjoint unit time intervals. -/
def UnitDedicatedProcessorMakespanFeasible (i : UnitDedicatedProcessorInstance) : Prop :=
  ∃ s : Fin i.2.1.length → ℕ, (∀ j, s j + 1 ≤ i.2.2) ∧
    ∀ j j', j ≠ j' → (∃ k ∈ i.2.1.get j, k ∈ i.2.1.get j') →
      s j + 1 ≤ s j' ∨ s j' + 1 ≤ s j

open Classical in
/-- `P|fixⱼ, pⱼ = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def unitDedicatedProcessorMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitDedicatedProcessorInstance) x with
  | some i => decide (WellFormed i ∧ UnitDedicatedProcessorMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitDedicatedProcessorMakespan
