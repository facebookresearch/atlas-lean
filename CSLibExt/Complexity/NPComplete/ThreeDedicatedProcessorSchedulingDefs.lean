/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-DEDICATED PROCESSOR SCHEDULING: definitions

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272,
doi:10.1016/0166-218X(94)90012-4, Theorem 2.3;
J. Błażewicz, P. Dell'Olmo, M. Drozdowski and M. G. Speranza, "Scheduling multiprocessor tasks on
three dedicated processors", Information Processing Letters 41 (1992), 275-280,
doi:10.1016/0020-0190(92)90172-R;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry
MINIMUM 3-DEDICATED PROCESSOR SCHEDULING.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDedicatedProcessorScheduling

/-- An instance: the tasks, each with its length and its list of required processors, and the
bound `K`. -/
abbrev ThreeDedicatedProcessorSchedulingInstance := List (ℕ × List ℕ) × ℕ

/-- Well-formedness of an instance: every task has a positive length and a nonempty set of
required processors, listed without repetitions, all below `3`; and `0 < K`. -/
def WellFormed (i : ThreeDedicatedProcessorSchedulingInstance) : Prop :=
  (∀ t ∈ i.1, 0 < t.1 ∧ t.2 ≠ [] ∧ t.2.Nodup ∧ ∀ k ∈ t.2, k < 3) ∧ 0 < i.2

/-- There are start times `s` with makespan at most `K` such that any two different tasks with a
common required processor are processed in disjoint time intervals. -/
def ThreeDedicatedProcessorSchedulingFeasible (i : ThreeDedicatedProcessorSchedulingInstance) :
    Prop :=
  ∃ s : Fin i.1.length → ℕ, (∀ j, s j + (i.1.get j).1 ≤ i.2) ∧
    ∀ j j', j ≠ j' → (∃ k ∈ (i.1.get j).2, k ∈ (i.1.get j').2) →
      s j + (i.1.get j).1 ≤ s j' ∨ s j' + (i.1.get j').1 ≤ s j

open Classical in
/-- 3-DEDICATED PROCESSOR SCHEDULING as a decision problem over bitstrings. -/
noncomputable def threeDedicatedProcessorSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeDedicatedProcessorSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ ThreeDedicatedProcessorSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeDedicatedProcessorScheduling
