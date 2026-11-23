/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR MULTIPROCESSOR-TASK SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFixedAllocationTotalCompletion

/-!
# TWO-PROCESSOR MULTIPROCESSOR-TASK SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME is NP-complete

This is `P2|fixᵢ|∑Cᵢ` (Brucker: `MPT2||∑Cᵢ`), multiprocessor tasks with prespecified processor
allocations on two processors.

INSTANCE: two processors `M₁, M₂`, each processing at most one task at a time; tasks `1, …, n`,
task `i` with a processing time `pᵢ ∈ ℤ⁺` and a prespecified nonempty set `fixᵢ ⊆ {M₁, M₂}` of
processors, all of which it requires simultaneously during an uninterrupted period of length
`pᵢ` (so two tasks whose sets intersect cannot overlap in time); and an integer `K`. QUESTION:
is there a schedule whose total completion time `∑ᵢ Cᵢ` is at most `K`, `Cᵢ` being the
completion time of task `i`?

Hoogeveen, van de Velde and Veltman prove the problem NP-hard in the ordinary sense
(Theorem 3.2) and leave its strong NP-hardness open; Cai, Lee and Li prove it NP-hard in the
strong sense. Brucker's Table 11.2 lists `MPT2||∑Cᵢ` as NP-hard in the strong sense.

The model is that of `WantedExt.Complexity.NPComplete.ThreeDedicatedProcessorSchedulingWanted`
(three processors, makespan objective), whose feasibility predicate carries the makespan bound
and so does not apply here. Processors are `0, 1`; the tasks are listed as pairs
`(pᵢ, fixᵢ)`, the processor set as a list without repetitions, and the tasks are `Fin n` for
`n` listed tasks. A schedule gives each task a start time `s i ∈ ℤ₀⁺`, with `Cᵢ = s i + pᵢ`; two
different tasks with a common processor occupy disjoint intervals (one finishes no later than
the other starts). Integral start times lose no generality, since the data are integers. The
bound `K` is a natural number (a negative `K` gives only no-instances), and start times at most
`K` form a certificate of polynomial size. Binary encoding of all numbers (the problem is
NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **TWO-PROCESSOR MULTIPROCESSOR-TASK SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME
(`P2|fixᵢ|∑Cᵢ`) is NP-complete.** Source: Cai, Lee and Li (1998); Hoogeveen, van de Velde and
Veltman (1994), Theorem 3.2 (NP-hardness in the ordinary sense). -/
public theorem_wanted twoProcessorFixedAllocationTotalCompletion_npComplete :
    twoProcessorFixedAllocationTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorFixedAllocationTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFixedAllocationTotalCompletion
