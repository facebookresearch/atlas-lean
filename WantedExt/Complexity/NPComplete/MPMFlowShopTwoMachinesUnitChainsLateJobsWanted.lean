/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM FLOW SHOP FMPM2|chains;p_ij=1|ΣU_i is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 10 (the MPM flow-shop model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `FMPM2|chains;p_ij=1|ΣU_i` as minimal NP-hard in the strong sense
("Single-machine problem");
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
public import WantedExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsLateJobsWanted
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMFlowShopTwoMachinesUnitChainsLateJobs

open MPMOpenShopTwoMachinesUnitChainsLateJobs
  (MPMOpenShopTwoMachinesUnitChainsLateJobsInstance WellFormed)
open MultipurposeFlowShopPrecedenceMakespan (IsPrecedenceSchedule completionTime)

/-!
# MPM FLOW SHOP FMPM2|chains;p_ij=1|ΣU_i is NP-complete

INSTANCE: machines `M_1, M_2`; an MPM flow shop with `r ≥ 1` stages and nonempty machine sets
`μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with unit processing times (`p_ij = 1`), where `O_ij` is processed by one
machine of `μ_j` and `O_i,j+1` cannot start before `O_ij` is completed; precedence constraints
forming chains (every job has at most one immediate predecessor and at most one immediate successor;
if `i` precedes `k`, no operation of `k` starts before `J_i` is completed); due dates `d_i`; and a
bound `K`. Each machine processes at most one operation at a time. QUESTION: is there a feasible
schedule with at most `K` late jobs (jobs `i` with `C_i > d_i`), where `C_i` is the completion time
of job `i` (that of its last operation)?

The MPM flow shop is Brucker's (*Scheduling Algorithms*, Chapter 10): each job has exactly `r`
operations, the `j`-th operation of every job is processed by one machine of the same set `μ_j`, the
machine sets are different, and the operations of a job are processed in the order of the stages.
The instance and its well-formedness are those of the two-machine MPM open shop
`OMPM2|chains;p_ij=1|ΣU_i` (`MPMOpenShopTwoMachinesUnitChainsLateJobsWanted`):
`MPMOpenShopTwoMachinesUnitChainsLateJobs.MPMOpenShopTwoMachinesUnitChainsLateJobsInstance` (the
machine sets as lists of machine indices `0, 1`, one due date per job, so `n` is the length of that
list and all processing times are `1`, the chain arcs, and `K`) and
`MPMOpenShopTwoMachinesUnitChainsLateJobs.WellFormed` (at least one stage, machine indices below
`2`, pairwise different nonempty sets, and chain arcs on the jobs). The schedule predicate is
`MultipurposeFlowShopPrecedenceMakespan.IsPrecedenceSchedule` of
`MultipurposeFlowShopPrecedenceMakespanWanted` (`FMPM|prec;p_ij=1|C_max`) for the chain arcs: unit
operations `(j, s)` with start times `σ j s` and machines `a j s ∈ μ_s`, operation `(j, s + 1)`
starting no earlier than operation `(j, s)` is completed, operations on one machine at different
times, and, for an arc `(i, k)`, every operation of `k` starting no earlier than `C_i`; `C_j` is
`MultipurposeFlowShopPrecedenceMakespan.completionTime`, the latest completion time of a job's
operations. With unit operations and integer data, integer start times lose no generality.

The single-machine problem `1|chains;p_i=1|ΣU_i` (`TardyTasksUnitChainsWanted`), strongly NP-hard by
Lenstra and Rinnooy Kan (1980), is the special case `r = 1`, `μ_1 = {M_1}`; Brucker and Knust list
`FMPM2|chains;p_ij=1|ΣU_i` as minimal NP-hard in the strong sense on that basis ("Single-machine
problem"). Binary encoding of all numbers. Membership in NP: the machines and start times are a
certificate; removing a time slot in which no operation runs keeps every constraint and increases no
completion time, so some optimal schedule has all `r n` start times below `r n`.

Encoding: the instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in `MetaMathlibExt.ComplexityTheory.NP`, plus a
polynomial-time many-one reduction from every language in `NP` (`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some MPM flow-shop schedule of the unit-time jobs on the two machines obeying the chain arcs has
at most `K` late jobs (jobs `i` with `C_i > d_i`). -/
def MPMFlowShopTwoMachinesUnitChainsLateJobsFeasible
    (i : MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) : Prop :=
  ∃ σ : Fin i.2.1.length → Fin i.1.length → ℕ, ∃ a : Fin i.2.1.length → Fin i.1.length → Fin 2,
    IsPrecedenceSchedule 2 i.1 i.2.2.1 σ a ∧
      (Finset.univ.filter fun j : Fin i.2.1.length =>
        i.2.1.get j < completionTime (fun _ _ => 1) σ j).card ≤ i.2.2.2

open Classical in
/-- `FMPM2|chains;p_ij=1|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def mpmFlowShopTwoMachinesUnitChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MPMOpenShopTwoMachinesUnitChainsLateJobsInstance) x with
  | some i => decide (WellFormed i ∧ MPMFlowShopTwoMachinesUnitChainsLateJobsFeasible i)
  | none => false

/-- **MPM FLOW SHOP FMPM2|chains;p_ij=1|ΣU_i is NP-complete.** Source: Brucker and Knust's
classification ("Single-machine problem": Lenstra and Rinnooy Kan (1980), `1|chains;p_i=1|ΣU_i`);
Brucker (2007), Chapter 10 (model). -/
public theorem_wanted mpmFlowShopTwoMachinesUnitChainsLateJobs_npComplete :
    mpmFlowShopTwoMachinesUnitChainsLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mpmFlowShopTwoMachinesUnitChainsLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.MPMFlowShopTwoMachinesUnitChainsLateJobs
