/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR MULTIPROCESSOR-TASK SCHEDULING TO MINIMIZE MAXIMUM LATENESS: definitions

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272,
doi:10.1016/0166-218X(94)90012-4, Theorem 2.8 (`P2|fixⱼ, rⱼ|C_max`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Table 11.2 (`MPT2||L_max`,
NP-hard in the strong sense, Hoogeveen et al.).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFixedAllocationMaxLateness

/-- An instance: the tasks, task `i` being the `i`-th triple `(pᵢ, fixᵢ, dᵢ)` of its processing
time, its list of required processors and its due date, and the bound `y` as a pair
`(y⁺, y⁻)` with `y = y⁺ - y⁻`. -/
abbrev TwoProcessorFixedAllocationMaxLatenessInstance := List (ℕ × List ℕ × ℕ) × (ℕ × ℕ)

/-- Well-formedness of an instance: there is at least one task, and every task has a positive
processing time and a nonempty set of required processors, listed without repetitions, all below
`2`. -/
def WellFormed (i : TwoProcessorFixedAllocationMaxLatenessInstance) : Prop :=
  i.1 ≠ [] ∧ ∀ t ∈ i.1, 0 < t.1 ∧ t.2.1 ≠ [] ∧ t.2.1.Nodup ∧ ∀ k ∈ t.2.1, k < 2

/-- There are start times `s` such that any two different tasks with a common required processor
are processed in disjoint time intervals, and every task `i` has lateness
`(s i + pᵢ) - dᵢ ≤ y⁺ - y⁻`. -/
def TwoProcessorFixedAllocationMaxLatenessFeasible
    (i : TwoProcessorFixedAllocationMaxLatenessInstance) : Prop :=
  ∃ s : Fin i.1.length → ℕ,
    (∀ j j', j ≠ j' → (∃ k ∈ (i.1.get j).2.1, k ∈ (i.1.get j').2.1) →
      s j + (i.1.get j).1 ≤ s j' ∨ s j' + (i.1.get j').1 ≤ s j) ∧
    ∀ j, s j + (i.1.get j).1 + i.2.2 ≤ (i.1.get j).2.2 + i.2.1

open Classical in
/-- `P2|fixᵢ|L_max` as a decision problem over bitstrings. -/
noncomputable def twoProcessorFixedAllocationMaxLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorFixedAllocationMaxLatenessInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorFixedAllocationMaxLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFixedAllocationMaxLateness
