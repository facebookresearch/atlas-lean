/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR MULTIPROCESSOR-TASK SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME: definitions

Source:
X. Cai, C.-Y. Lee and C.-L. Li, "Minimizing total completion time in two-processor task systems
with prespecified processor allocations", Naval Research Logistics 45 (1998), 231-242,
doi:10.1002/(SICI)1520-6750(199803)45:2<231::AID-NAV7>3.0.CO;2-9;
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272,
doi:10.1016/0166-218X(94)90012-4, Theorem 3.2;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Table 11.2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFixedAllocationTotalCompletion

/-- An instance: the tasks, task `i` being the `i`-th pair `(pᵢ, fixᵢ)` of its processing time
and its list of required processors, and the bound `K`. -/
abbrev TwoProcessorFixedAllocationTotalCompletionInstance := List (ℕ × List ℕ) × ℕ

/-- Well-formedness of an instance: every task has a positive processing time and a nonempty
set of required processors, listed without repetitions, all below `2`. -/
def WellFormed (i : TwoProcessorFixedAllocationTotalCompletionInstance) : Prop :=
  ∀ t ∈ i.1, 0 < t.1 ∧ t.2 ≠ [] ∧ t.2.Nodup ∧ ∀ k ∈ t.2, k < 2

/-- There are start times `s` such that any two different tasks with a common required processor
are processed in disjoint time intervals, and the total completion time
`∑ᵢ (s i + pᵢ)` is at most `K`. -/
def TwoProcessorFixedAllocationTotalCompletionFeasible
    (i : TwoProcessorFixedAllocationTotalCompletionInstance) : Prop :=
  ∃ s : Fin i.1.length → ℕ,
    (∀ j j', j ≠ j' → (∃ k ∈ (i.1.get j).2, k ∈ (i.1.get j').2) →
      s j + (i.1.get j).1 ≤ s j' ∨ s j' + (i.1.get j').1 ≤ s j) ∧
    ∑ j, (s j + (i.1.get j).1) ≤ i.2

open Classical in
/-- `P2|fixᵢ|∑Cᵢ` as a decision problem over bitstrings. -/
noncomputable def twoProcessorFixedAllocationTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorFixedAllocationTotalCompletionInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorFixedAllocationTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFixedAllocationTotalCompletion
