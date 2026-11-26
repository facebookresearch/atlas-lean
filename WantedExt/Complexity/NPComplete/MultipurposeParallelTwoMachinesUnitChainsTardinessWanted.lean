/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS AND UNIT TIMES, total tardiness
(`PMPM2|chains;p_i=1|ΣT_i`) is NP-complete

Source:
J. Y.-T. Leung and G. H. Young, "Minimizing total tardiness on a single machine with
precedence constraints", ORSA Journal on Computing 2 (1990), 346-352,
doi:10.1287/ijoc.2.4.346 (`1|chains, pⱼ = 1|∑ Tⱼ`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Multi-purpose machine problems" (`PMPM2|chains; p_i=1|ΣT_i`, minimal NP-hard in the
strong sense, as a single-machine problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsTardiness

open MultiPurposeJobShopThreeJobs (Operation opLength IsMPMJobShopSchedule)
open UnitFlowShopPrecedenceMakespan (Prec)
open MultipurposeParallelTwoMachinesUnitChainsMakespan
  (MultipurposeParallelTwoMachinesUnitChainsMakespanInstance)

/-!
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS AND UNIT TIMES, total tardiness, is
NP-complete

INSTANCE: `m = 2` identical parallel machines; jobs `1, …, n`, each with processing time
`pᵢ = 1`, a nonempty set `μᵢ ⊆ {M₁, M₂}` of eligible machines and a due date `dᵢ ∈ ℤ₀⁺`;
precedence constraints that form a set of chains (every job has at most one immediate
predecessor and at most one immediate successor), where `i` preceding `j` means that `j` cannot
start before `i` is completed; and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a schedule, every job on
one machine of its set, whose total tardiness `Σᵢ max(0, Cᵢ - dᵢ)` is at most `K`, where `Cᵢ` is
the completion time of job `i`?

This is `PMPM2|chains; p_i=1|ΣT_i` in the Brucker-Knust classification. When every job has the
machine set `{M₁}`, it is the single-machine problem `1|chains, p_j = 1|ΣT_j`
(`ChainsUnitTaskTardinessWanted`), which Leung and Young prove NP-hard in the strong sense; the
Brucker-Knust classification records this entry as minimal NP-hard in the strong sense for that
reason. The machines, jobs, machine sets and chains are those of `PMPM2|chains; p_i=1|C_max`
(`MultipurposeParallelTwoMachinesUnitChainsMakespanWanted`): an instance is that module's
instance (an MPM job-shop instance with `m = 2` in which every job is one unit operation, its
bound component being `K`, together with the precedence arcs) and the due dates, one per job,
listed in job order; `WellFormed` is that module's well-formedness (machine sets nonempty and in
`{1, 2}`, unit single-operation jobs, acyclic arcs naming jobs that form chains) plus one due
date per job. A schedule is an MPM schedule (`MultiPurposeJobShopThreeJobs.IsMPMJobShopSchedule`)
obeying the arcs, as in that module. Every job has exactly one operation, so the total tardiness
is the sum over the operations `t` of `σ t + 1 - d_j` for the job `j` of `t`, where natural
subtraction gives `max(0, C_j - d_j)`. Integral start times lose no generality, since the data
are integers; membership in NP holds because removing a time slot in which no job runs keeps a
schedule feasible and increases no tardiness, so a schedule meeting `K` can be taken with all
start times below `n`. Binary encoding of all numbers; the source proves NP-hardness in the
strong sense, which this statement does not record.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: a `PMPM2|chains; p_i=1|C_max` instance (the MPM job-shop instance, whose bound
component is `K`, and the precedence arcs) and the due dates, job `j` having the `j`-th listed
due date `d_j`. -/
abbrev MultipurposeParallelTwoMachinesUnitChainsTardinessInstance :=
  MultipurposeParallelTwoMachinesUnitChainsMakespanInstance × List ℕ

/-- The due date `d_j` of job `j`. -/
def dueDate (i : MultipurposeParallelTwoMachinesUnitChainsTardinessInstance)
    (j : Fin i.1.1.2.1.length) : ℕ :=
  i.2.getD j 0

/-- Well-formedness of an instance: a well-formed `PMPM2|chains; p_i=1|C_max` instance (two
machines, nonempty machine sets in `{1, 2}`, unit single-operation jobs, acyclic arcs naming jobs
that form chains) and one due date per job. -/
def WellFormed (i : MultipurposeParallelTwoMachinesUnitChainsTardinessInstance) : Prop :=
  MultipurposeParallelTwoMachinesUnitChainsMakespan.WellFormed i.1 ∧
    i.2.length = i.1.1.2.1.length

/-- Some MPM schedule of the jobs obeys the precedence arcs and has total tardiness at most `K`:
the sum, over the operations `t` (one per job), of `σ t + p_t - d_j` for the job `j` of `t`. -/
def MultipurposeParallelTwoMachinesUnitChainsTardinessFeasible
    (i : MultipurposeParallelTwoMachinesUnitChainsTardinessInstance) : Prop :=
  ∃ a σ : Operation i.1.1 → ℕ, IsMPMJobShopSchedule i.1.1 a σ ∧
    (∀ t t' : Operation i.1.1, Prec i.1.2 t.1 t'.1 → σ t + opLength i.1.1 t ≤ σ t') ∧
    (∑ t : Operation i.1.1, (σ t + opLength i.1.1 t - dueDate i t.1)) ≤ i.1.1.2.2

open Classical in
/-- `PMPM2|chains; p_i=1|ΣT_i` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelTwoMachinesUnitChainsTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelTwoMachinesUnitChainsTardinessInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultipurposeParallelTwoMachinesUnitChainsTardinessFeasible i)
  | none => false

/-- **`PMPM2|chains; p_i=1|ΣT_i` is NP-complete.** Source: Leung and Young (1990), for the
single-machine case in which every machine set is `{M₁}`; Brucker-Knust classification. -/
public theorem_wanted multipurposeParallelTwoMachinesUnitChainsTardiness_npComplete :
    multipurposeParallelTwoMachinesUnitChainsTardinessDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelTwoMachinesUnitChainsTardinessDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsTardiness
