/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS AND UNIT TIMES, number of late jobs
(`PMPM2|chains; pᵢ = 1|ΣUᵢ`) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 10 (multi-purpose machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Parallel machine problems with
multi-purpose machines", which lists `PMPM2|chains;p_i=1|ΣU_i` as minimal NP-hard in the strong
sense ("Single-machine problem");
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3, Theorem 1 (the single-machine problem `1|chains;p_j=1|ΣU_j`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import WantedExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsWanted
public import WantedExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsMakespanWanted
public import WantedExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsLateJobs

open MultiPurposeJobShopThreeJobs (Operation opLength IsMPMJobShopSchedule)
open MultipurposeParallelTwoMachinesUnitChainsMakespan
  (MultipurposeParallelTwoMachinesUnitChainsMakespanInstance)
open UnitFlowShopPrecedenceMakespan (Prec)

/-!
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH CHAINS AND UNIT TIMES, number of late jobs

INSTANCE: `m = 2` identical parallel machines; jobs `1, …, n`, each with processing time `pᵢ = 1`, a
nonempty set `μᵢ ⊆ {M₁, M₂}` of eligible machines and a due date `dᵢ`; precedence constraints that
form a set of chains (every job has at most one immediate predecessor and at most one immediate
successor), where `i` preceding `j` means that `j` cannot start before `i` is completed; and an
integer `K`. QUESTION: is there a schedule, every job on one machine of its set, with at most `K`
late jobs (jobs `i` with `Cᵢ > dᵢ`), where `Cᵢ` is the completion time of job `i`?

Brucker's multi-purpose machine model (*Scheduling Algorithms*, Chapter 10): every job `i` has a set
`μᵢ ⊆ {M₁, …, M_m}` and is processed by exactly one machine of `μᵢ`, each machine processing at most
one job at a time; with single-operation jobs and identical machines this is `PMPM`. The instance is
a `PMPM2|chains; pᵢ = 1|C_max` instance (`MultipurposeParallelTwoMachinesUnitChainsMakespanWanted`:
an MPM job-shop instance with the number of machines, the jobs as single operations `(pᵢ, μᵢ)` and a
bound, plus the chain arcs), whose bound is here the bound `K` on the number of late jobs, together
with the list of due dates, one per job. Well-formedness is that problem's `WellFormed` (two
machines, nonempty machine sets in `{1, 2}`, one unit operation per job, arcs naming jobs, acyclic,
forming chains) and one due date per job. A schedule is, as there, an MPM job-shop schedule
(`IsMPMJobShopSchedule`) in which `σᵢ + pᵢ ≤ σ_k` for every arc `(i, k)`. Every job has exactly one
operation, so the operations are the jobs, and the late operations are counted. Integral start times
lose no generality.

The single-machine problem `1|chains;p_i=1|ΣU_i` (`TardyTasksUnitChainsWanted`), strongly NP-hard by
Lenstra and Rinnooy Kan (1980), is the special case in which every `μᵢ` is `{M₁}`; Brucker and Knust
list `PMPM2|chains;p_i=1|ΣU_i` as minimal NP-hard in the strong sense on that basis ("Single-machine
problem"). Binary encoding of all numbers. Membership in NP: the machines and start times are a
certificate; removing a time slot in which no job runs keeps every constraint and increases no
completion time, so some optimal schedule has all start times below `n`.

Encoding: the instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in `MetaMathlibExt.ComplexityTheory.NP`, plus a
polynomial-time many-one reduction from every language in `NP` (`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: a `PMPM2|chains; pᵢ = 1|C_max` instance (whose bound is the bound `K` on the number
of late jobs) and the due dates `dᵢ`, job `j` having the `j`-th listed due date. -/
abbrev MultipurposeParallelTwoMachinesUnitChainsLateJobsInstance :=
  MultipurposeParallelTwoMachinesUnitChainsMakespanInstance × List ℕ

/-- Well-formedness of an instance: a well-formed `PMPM2|chains; pᵢ = 1|C_max` instance and one due
date per job. -/
def WellFormed (i : MultipurposeParallelTwoMachinesUnitChainsLateJobsInstance) : Prop :=
  MultipurposeParallelTwoMachinesUnitChainsMakespan.WellFormed i.1 ∧
    i.2.length = i.1.1.2.1.length

/-- Some MPM schedule of the jobs obeys the precedence arcs and has at most `K` late jobs: jobs
whose operation `t` completes after the due date of its job, `d < σ t + p_t`. -/
def MultipurposeParallelTwoMachinesUnitChainsLateJobsFeasible
    (i : MultipurposeParallelTwoMachinesUnitChainsLateJobsInstance) : Prop :=
  ∃ a σ : Operation i.1.1 → ℕ, IsMPMJobShopSchedule i.1.1 a σ ∧
    (∀ t t' : Operation i.1.1, Prec i.1.2 t.1 t'.1 → σ t + opLength i.1.1 t ≤ σ t') ∧
    (Finset.univ.filter fun t : Operation i.1.1 =>
      i.2.getD t.1 0 < σ t + opLength i.1.1 t).card ≤ i.1.1.2.2

open Classical in
/-- `PMPM2|chains; pᵢ = 1|ΣUᵢ` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelTwoMachinesUnitChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelTwoMachinesUnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeParallelTwoMachinesUnitChainsLateJobsFeasible i)
  | none => false

/-- **MPM PARALLEL MACHINES `PMPM2|chains; pᵢ = 1|ΣUᵢ` is NP-complete.** Source: Brucker and Knust's
classification ("Single-machine problem": Lenstra and Rinnooy Kan (1980), `1|chains;p_i=1|ΣU_i`);
Brucker (2007), Chapter 10 (model). -/
public theorem_wanted multipurposeParallelTwoMachinesUnitChainsLateJobs_npComplete :
    multipurposeParallelTwoMachinesUnitChainsLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelTwoMachinesUnitChainsLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesUnitChainsLateJobs
