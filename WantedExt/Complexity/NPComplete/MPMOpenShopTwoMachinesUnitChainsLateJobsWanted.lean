/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
# MPM OPEN SHOP OMPM2|chains;p_ij=1|ΣU_i is NP-complete

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1; P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007),
doi:10.1007/978-3-540-69516-5, Chapter 10 (the MPM open-shop model); P. Brucker and S. Knust,
*Complexity results for scheduling problems*, http://www2.informatik.uni-osnabrueck.de/knust/class/,
class "Shop problems with multipurpose machines", which lists `OMPM2|chains;p_ij=1|ΣU_i` as minimal
NP-hard in the strong sense, citing Timkovsky (2003), and class "Open-shop problems without
preemption", which lists the special case `O2|p_ij=1;chains|ΣU_i` as minimal NP-hard in the strong
sense, citing Timkovsky (2003).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsLateJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsLateJobs

open F3UnitChainsLateJobs (ChainsWellFormed)
open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopPrecedenceSchedule)

/-!
# MPM OPEN SHOP OMPM2|chains;p_ij=1|ΣU_i is NP-complete

INSTANCE: machines `M_1, M_2`; an MPM open shop with `r ≥ 1` stages and nonempty machine sets
`μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with unit processing times (`p_ij = 1`), where `O_ij` is processed by one
machine of `μ_j`, and the operations of a job are processed in any order but no two of them at the
same time; precedence constraints forming chains (every job has at most one immediate predecessor
and at most one immediate successor; if `i` precedes `k`, no operation of `k` starts before `J_i` is
completed); due dates `d_i`; and a bound `K`. Each machine processes at most one operation at a
time. QUESTION: is there a feasible schedule with at most `K` late jobs (jobs `i` with `C_i > d_i`),
where `C_i` is the completion time of job `i` (that of its last operation)?

The MPM open shop is Brucker's (*Scheduling Algorithms*, Chapter 10): MPM open-shop problems are
defined like MPM flow-shop problems (each job has exactly `r` operations, the `j`-th operation of
every job is processed by a machine of the same set `μ_j`, and the machine sets are different), but
with no precedence constraints between the operations of a job. The instance lists the machine sets
(machine indices `0, 1`), one due date per job (so `n` is the length of that list; all processing
times are `1`), the chain arcs and `K`. Well-formedness is the MPM machine environment of
`MultipurposeFlowShopPrecedenceMakespanWanted` with two machines (`StagesWellFormed 2`: at least one
stage, machine indices below `2`, pairwise different sets) with nonempty sets, and the chain
condition of `F3UnitChainsLateJobsWanted` (`ChainsWellFormed`: arcs between listed jobs, no repeated
arc, at most one successor and one predecessor per job, no cycle). The schedule predicate is
`IsMPMOpenShopPrecedenceSchedule` of `MultipurposeOpenShopPrecedenceMakespanWanted` for the chain
arcs: unit operations `(j, s)` with start times `σ j s` and machines `a j s ∈ μ_s`, operations of
one job and operations on one machine at different times, and, for an arc `(i, k)`, every operation
of `k` starting no earlier than `C_i`; `C_j` is
`MultipurposeFlowShopPrecedenceMakespan.completionTime`, the latest completion time of a job's
operations. With unit operations and integer data, integer start times lose no generality.

The classical open shop `O2|p_ij=1;chains|ΣU_i` is the special case `r = 2`, `μ_1 = {M_1}`,
`μ_2 = {M_2}`. Brucker and Knust list both problems as minimal NP-hard in the strong sense,
crediting Timkovsky (2003), whose full text was not available. Binary encoding of all numbers.
Membership in NP: the machines and start times are a certificate; removing a time slot in which no
operation runs keeps every constraint and increases no completion time, so some optimal schedule has
all `r n` start times below `r n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MPM OPEN SHOP OMPM2|chains;p_ij=1|ΣU_i is NP-complete.** Source: Timkovsky (2003), as recorded
in the Brucker-Knust classification (with the special case `O2|p_ij=1;chains|ΣU_i`); Brucker (2007),
Chapter 10 (model). -/
public theorem_wanted mpmOpenShopTwoMachinesUnitChainsLateJobs_npComplete :
    mpmOpenShopTwoMachinesUnitChainsLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mpmOpenShopTwoMachinesUnitChainsLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsLateJobs
