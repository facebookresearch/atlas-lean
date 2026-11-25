/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR PARALLEL TASK SCHEDULING `P3|size_i|Cmax` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS8] MULTIPROCESSOR SCHEDULING (the
case in which every task has size `1`);
J. Du and J. Y.-T. Leung, "Complexity of scheduling parallel task systems", SIAM Journal on
Discrete Mathematics 2 (1989), 473-487, doi:10.1137/0402042 (pseudo-polynomial algorithm for
three processors);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Section 11.4 (tasks of type
`sizeᵢ`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorParallelTaskMakespan

/-!
# THREE-PROCESSOR PARALLEL TASK SCHEDULING `P3|size_i|Cmax` is NP-complete

INSTANCE: three identical processors, each executing at most one task at a time; `n` tasks, task
`i` with a processing time `pᵢ ∈ ℤ⁺` and a size `sizeᵢ ∈ {1, 2, 3}` (the task uses `sizeᵢ`
processors, any of them, simultaneously during its whole uninterrupted processing); and an
integer `K`. QUESTION: is there a schedule with makespan `maxᵢ Cᵢ ≤ K`, where `Cᵢ` is the
completion time of task `i`?

With every `sizeᵢ = 1` the problem is `P3||C_max`, MULTIPROCESSOR SCHEDULING ([SS8]) with
`m = 3`, which is NP-complete: [SS8] is NP-complete for `m = 2`, and adding one task of length `K`
reduces `m = 2` to `m = 3`. The problem is therefore NP-complete in the ordinary sense; Du and
Leung solve it in pseudo-polynomial time for two and three processors and prove it NP-hard in
the strong sense for five processors, and the Brucker-Knust classification lists
`P3|size_i|C_max` as maximal pseudo-polynomially solvable.

Tasks are listed one per entry as `(pᵢ, sizeᵢ)`; tasks are `Fin n`. As in
`WantedExt.Complexity.NPComplete.TwoProcessorTaskSizeReleaseDatesWanted` (two processors, with
release dates), a schedule is given by start times and processors are not named: start times
admit an assignment of processors, each task keeping its processors throughout its processing,
exactly when at every time the sizes of the running tasks sum to at most `3` (replacing each task
by `sizeᵢ` copies of its interval gives an interval graph, whose chromatic number is its largest
clique). Start times are natural numbers, since the data are integers. The bound `K` is a natural
number (a negative `K` gives only no-instances), and the `n` start times, each at most `K`, form
a certificate of polynomial size (the running set changes only at the `2n` start and completion
times). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the tasks `(pᵢ, sizeᵢ)` (processing time and size), one per entry, and the
bound `K`. -/
abbrev ThreeProcessorParallelTaskMakespanInstance := List (ℕ × ℕ) × ℕ

/-- Well-formedness: every task has a positive processing time and size `1`, `2` or `3`. -/
def WellFormed (i : ThreeProcessorParallelTaskMakespanInstance) : Prop :=
  ∀ t ∈ i.1, 0 < t.1 ∧ 1 ≤ t.2 ∧ t.2 ≤ 3

/-- There are start times `s` such that every task completes by `K`, and at every time `t` the
tasks running at `t` (`s j ≤ t < s j + p_j`) have total size at most `3`. -/
def ThreeProcessorParallelTaskMakespanFeasible
    (i : ThreeProcessorParallelTaskMakespanInstance) : Prop :=
  ∃ s : Fin i.1.length → ℕ, (∀ j, s j + (i.1.get j).1 ≤ i.2) ∧
    ∀ t : ℕ, ∑ j ∈ Finset.univ.filter (fun j => s j ≤ t ∧ t < s j + (i.1.get j).1),
      (i.1.get j).2 ≤ 3

open Classical in
/-- `P3|size_i|Cmax` as a decision problem over bitstrings. -/
noncomputable def threeProcessorParallelTaskMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeProcessorParallelTaskMakespanInstance) x with
  | some i => decide (WellFormed i ∧ ThreeProcessorParallelTaskMakespanFeasible i)
  | none => false

/-- **THREE-PROCESSOR PARALLEL TASK SCHEDULING `P3|size_i|Cmax` is NP-complete.** Source: Garey
and Johnson (1979), [SS8], with every size `1`; Du and Leung (1989). -/
public theorem_wanted threeProcessorParallelTaskMakespan_npComplete :
    threeProcessorParallelTaskMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeProcessorParallelTaskMakespanDec

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorParallelTaskMakespan
