/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEDICATED-PROCESSOR TOTAL COMPLETION TIME (P|fixⱼ, pⱼ = 1|∑ Cⱼ): definitions

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272,
doi:10.1016/0166-218X(94)90012-4, Theorem 3.5 (`P|fixⱼ, pⱼ = 1|∑ Cⱼ` is NP-hard in the strong
sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Multiprocessor task problems with
dedicated processors", which lists the problem as minimal NP-hard with this attribution.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitDedicatedProcessorMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitDedicatedProcessorCompletionTime

open UnitDedicatedProcessorMakespan (UnitDedicatedProcessorInstance WellFormed)

/-- There are start times `s` with total completion time `∑ⱼ (s j + 1)` at most `K` such that
any two different tasks with a common processor are processed in disjoint unit time
intervals. -/
def UnitDedicatedProcessorCompletionTimeFeasible (i : UnitDedicatedProcessorInstance) : Prop :=
  ∃ s : Fin i.2.1.length → ℕ, ∑ j, (s j + 1) ≤ i.2.2 ∧
    ∀ j j', j ≠ j' → (∃ k ∈ i.2.1.get j, k ∈ i.2.1.get j') →
      s j + 1 ≤ s j' ∨ s j' + 1 ≤ s j

open Classical in
/-- `P|fixⱼ, pⱼ = 1|∑ Cⱼ` as a decision problem over bitstrings. -/
noncomputable def unitDedicatedProcessorCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitDedicatedProcessorInstance) x with
  | some i => decide (WellFormed i ∧ UnitDedicatedProcessorCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitDedicatedProcessorCompletionTime
