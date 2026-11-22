/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEDICATED-PROCESSOR SCHEDULING `P2|chains;p_i=1;fix_i|C_max` is NP-complete

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994),
259-272, doi:10.1016/0166-218X(94)90012-4, Theorem 2.7;
J. Błażewicz, J. K. Lenstra and A. H. G. Rinnooy Kan, "Scheduling subject to resource
constraints: classification and complexity", Discrete Applied Mathematics 5 (1983), 11-24,
doi:10.1016/0166-218X(83)90012-4 (the approach of the proof);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Multiprocessor task problems with dedicated processors"
(`P2|chains;p_i=1;fix_i|C_max`, minimal NP-hard in the strong sense).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.F3UnitChainsLateJobsWanted
public import WantedExt.Complexity.NPComplete.UnitDedicatedProcessorMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitDedicatedChainsMakespan

open MetaMathlibExt.Complexity.NPComplete.F3UnitChainsLateJobs (ChainsWellFormed)
open MetaMathlibExt.Complexity.NPComplete.UnitDedicatedProcessorMakespan
  (UnitDedicatedProcessorInstance)

/-!
# DEDICATED-PROCESSOR SCHEDULING `P2|chains;p_i=1;fix_i|C_max` is NP-complete

INSTANCE: `m = 2` processors, each processing at most one task at a time; tasks `1, …, n`, each
with unit processing time `p_i = 1` and a prespecified set `fix_i ⊆ {1, 2}` of processors, all
of which it requires simultaneously during its processing (so two tasks whose sets intersect
cannot overlap in time); a precedence relation on the tasks consisting of chains (every task has
at most one immediate predecessor and at most one immediate successor): if `i` precedes `j`,
then `j` cannot start before `i` is completed; and a positive integer `K`. QUESTION: is there a
feasible schedule with makespan `max_i C_i ≤ K`, where `C_i` is the completion time of task `i`?

This is `P|fix_j, p_j = 1|C_max` (`UnitDedicatedProcessorMakespanWanted`) restricted to `m = 2`
processors, with chain precedence constraints added. The instance extends that problem's
instance (`m`, the processor sets `fix_i` as nonempty lists without repetitions of processors
below `m`, and `K > 0`, with its well-formedness reused) by the chain arcs `(i, j)` (task `i`
immediately precedes task `j`), with the chain conditions of `F3UnitChainsLateJobs.ChainsWellFormed`
(distinct arcs naming tasks, no task with two immediate successors or two immediate
predecessors, no cycle). A schedule gives each task a start time `s i ∈ ℕ` and the completion
time `C_i = s i + 1`; two different tasks with a common processor run in disjoint unit time
intervals, and an arc `(i, j)` requires `s i + 1 ≤ s j` (the whole precedence relation follows
by transitivity). Integral start times lose no generality for unit tasks without release dates.
Binary encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: an instance `(m, fix, K)` of `P|fix_j, p_j = 1|C_max` and the chain arcs
`(i, j)` (task `i` immediately precedes task `j`). -/
abbrev TwoProcessorUnitDedicatedChainsInstance := UnitDedicatedProcessorInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: it is well-formed for `P|fix_j, p_j = 1|C_max` (nonempty
processor sets without repetitions, processors below `m`, `0 < m`, `0 < K`), `m = 2`, and the
arcs form chains on the tasks. -/
def WellFormed (i : TwoProcessorUnitDedicatedChainsInstance) : Prop :=
  UnitDedicatedProcessorMakespan.WellFormed i.1 ∧ i.1.1 = 2 ∧
    ChainsWellFormed i.1.2.1.length i.2

/-- `s` (start times of the unit tasks) is a schedule: two different tasks with a common
processor run in disjoint unit time intervals, and every chain arc `(j, j')` has
`s j + 1 ≤ s j'`. -/
def IsSchedule (i : TwoProcessorUnitDedicatedChainsInstance) (s : Fin i.1.2.1.length → ℕ) :
    Prop :=
  (∀ j j', j ≠ j' → (∃ k ∈ i.1.2.1.get j, k ∈ i.1.2.1.get j') →
    s j + 1 ≤ s j' ∨ s j' + 1 ≤ s j) ∧
    ∀ j j' : Fin i.1.2.1.length, ((j : ℕ), (j' : ℕ)) ∈ i.2 → s j + 1 ≤ s j'

/-- Some schedule has makespan at most `K`: every `s j + 1 ≤ K`. -/
def TwoProcessorUnitDedicatedChainsMakespanFeasible
    (i : TwoProcessorUnitDedicatedChainsInstance) : Prop :=
  ∃ s, IsSchedule i s ∧ ∀ j, s j + 1 ≤ i.1.2.2

open Classical in
/-- `P2|chains;p_i=1;fix_i|C_max` as a decision problem over bitstrings. -/
noncomputable def twoProcessorUnitDedicatedChainsMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitDedicatedChainsInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitDedicatedChainsMakespanFeasible i)
  | none => false

/-- **DEDICATED-PROCESSOR SCHEDULING `P2|chains;p_i=1;fix_i|C_max` is NP-complete.** Source:
Hoogeveen, van de Velde and Veltman (1994), Theorem 2.7. -/
public theorem_wanted twoProcessorUnitDedicatedChainsMakespan_npComplete :
    twoProcessorUnitDedicatedChainsMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitDedicatedChainsMakespanDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitDedicatedChainsMakespan
