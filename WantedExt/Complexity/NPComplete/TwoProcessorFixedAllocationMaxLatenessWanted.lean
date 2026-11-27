/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR MULTIPROCESSOR-TASK SCHEDULING TO MINIMIZE MAXIMUM LATENESS is NP-complete

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272,
doi:10.1016/0166-218X(94)90012-4, Theorem 2.8 (`P2|fixⱼ, rⱼ|C_max`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Table 11.2 (`MPT2||L_max`,
NP-hard in the strong sense, Hoogeveen et al.).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFixedAllocationMaxLateness

/-!
# TWO-PROCESSOR MULTIPROCESSOR-TASK SCHEDULING TO MINIMIZE MAXIMUM LATENESS is NP-complete

This is `P2|fixᵢ|L_max` (Brucker: `MPT2||L_max`), multiprocessor tasks with prespecified
processor allocations on two processors.

INSTANCE: two processors `M₁, M₂`, each processing at most one task at a time; tasks `1, …, n`,
task `i` with a processing time `pᵢ ∈ ℤ⁺`, a prespecified nonempty set `fixᵢ ⊆ {M₁, M₂}` of
processors, all of which it requires simultaneously during an uninterrupted period of length
`pᵢ` (so two tasks whose sets intersect cannot overlap in time), and a due date `dᵢ`; and an
integer `y`. QUESTION: is there a schedule whose maximum lateness `L_max = maxᵢ (Cᵢ - dᵢ)` is
at most `y`, `Cᵢ` being the completion time of task `i`?

Brucker's Table 11.2 lists `MPT2||L_max` as NP-hard in the strong sense, citing Hoogeveen, van
de Velde and Veltman. They prove `P2|fixⱼ, rⱼ|C_max` NP-hard in the strong sense (Theorem 2.8),
and the two problems are equivalent by reversing time: a schedule `s` of makespan at most `C`
respecting release dates `rᵢ` gives the schedule `C - (s i + pᵢ)`, which completes every task
`i` by the due date `dᵢ = C - rᵢ`, and conversely.

Processors are `0, 1`; the tasks are listed as triples `(pᵢ, fixᵢ, dᵢ)`, the processor set as
a list without repetitions, and the tasks are `Fin n` for `n` listed tasks. A schedule gives
each task a start time `s i ∈ ℤ₀⁺`, with `Cᵢ = s i + pᵢ`; two different tasks with a common
processor occupy disjoint intervals (one finishes no later than the other starts), as in
`WantedExt.Complexity.NPComplete.ThreeDedicatedProcessorSchedulingWanted`. Integral start
times lose no generality, since the data are integers. Due dates are natural numbers (adding a
constant to every due date and subtracting it from `y` changes nothing). The bound `y` is an
integer, encoded as a pair `(y⁺, y⁻)` of naturals representing `y⁺ - y⁻`, as in
`WantedExt.Complexity.NPComplete.TwoProcessorFlowShopMaximumLatenessWanted`; `Cᵢ - dᵢ ≤ y` is
stated over `ℕ` as `Cᵢ + y⁻ ≤ dᵢ + y⁺`, so start times at most `maxᵢ dᵢ + y⁺` form a
certificate of polynomial size. There is at least one task, so that `L_max` is defined. Binary
encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **TWO-PROCESSOR MULTIPROCESSOR-TASK SCHEDULING TO MINIMIZE MAXIMUM LATENESS
(`P2|fixᵢ|L_max`) is NP-complete.** Source: Hoogeveen, van de Velde and Veltman (1994),
Theorem 2.8, by reversing time; Brucker (2007), Table 11.2. -/
public theorem_wanted twoProcessorFixedAllocationMaxLateness_npComplete :
    twoProcessorFixedAllocationMaxLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorFixedAllocationMaxLatenessDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFixedAllocationMaxLateness
