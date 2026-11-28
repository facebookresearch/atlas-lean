/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP OMPM2|chains;p_ij=1|ΣT_i is NP-complete

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (the full text was not available);
J. Y.-T. Leung and G. H. Young, "Minimizing total tardiness on a single machine with precedence
constraints", ORSA Journal on Computing 2 (1990), 346-352, doi:10.1287/ijoc.2.4.346
(`1|chains, p_j = 1|ΣT_j`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM open-shop
model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Shop problems with
multipurpose machines" (`OMPM2|chains;p_ij=1|ΣT_i`, minimal NP-hard in the strong sense, credited
to Timkovsky (2003)) and class "Open-shop problems without preemption" (the special case
`O2|p_ij=1;chains|ΣT_i`, minimal NP-hard in the strong sense, credited to Timkovsky (2003)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsTotalTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsTotalTardiness

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopPrecedenceSchedule)
open MPMOpenShopTwoMachinesUnitChainsLateJobs
  (MPMOpenShopTwoMachinesUnitChainsLateJobsInstance WellFormed)

/-!
# MPM OPEN SHOP OMPM2|chains;p_ij=1|ΣT_i is NP-complete

INSTANCE: machines `M_1, M_2`; an MPM open shop with `r ≥ 1` stages and nonempty machine sets
`μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with unit processing times (`p_ij = 1`), where `O_ij` is processed by
one machine of `μ_j`, and the operations of a job are processed in any order but no two of them at
the same time; precedence constraints forming chains (every job has at most one immediate
predecessor and at most one immediate successor; if `i` precedes `k`, no operation of `k` starts
before `J_i` is completed); due dates `d_i`; and a bound `K`. Each machine processes at most one
operation at a time. QUESTION: is there a feasible schedule with total tardiness
`Σ_i max(0, C_i - d_i) ≤ K`, where `C_i` is the completion time of job `i` (that of its last
operation)?

The instance and its well-formedness are those of `OMPM2|chains;p_ij=1|ΣU_i`
(`MPMOpenShopTwoMachinesUnitChainsLateJobsWanted`), reused unchanged: the stage machine sets
(machine indices `0, 1`), one due date per job (so `n` is the length of that list; all
processing times are `1`), the chain arcs and `K`; a two-machine MPM environment with nonempty,
pairwise different machine sets and chain arcs on the jobs. The MPM open shop is Brucker's
(*Scheduling Algorithms*, Chapter 10): MPM open-shop problems are defined like MPM flow-shop
problems (each job has exactly `r` operations, the `j`-th operation of every job is processed by a
machine of the same set `μ_j`), but with no precedence constraints between the operations of a
job. The schedule predicate is `IsMPMOpenShopPrecedenceSchedule` of
`MultipurposeOpenShopPrecedenceMakespanWanted` for the chain arcs, and `C_j` is
`MultipurposeFlowShopPrecedenceMakespan.completionTime`, the latest completion time of a job's
operations, as in that module. Natural subtraction `C_j - d_j` is `max(0, C_j - d_j)`. With unit
operations and integer data, integer start times lose no generality.

The classical open shop `O2|p_ij=1;chains|ΣT_i` (`O2UnitChainsTotalTardinessWanted`) is the
special case `r = 2`, `μ_1 = {M_1}`, `μ_2 = {M_2}`. Brucker and Knust list both problems as
minimal NP-hard in the strong sense, crediting Timkovsky (2003), whose full text was not
available. The case `r = 1`, `μ_1 = {M_1}` is the single-machine problem `1|chains, p_j = 1|ΣT_j`
(`ChainsUnitTaskTardinessWanted`), which Leung and Young prove NP-hard in the strong sense. Binary
encoding of all numbers. Membership in NP: the machines and start times are a certificate;
removing a time slot in which no operation runs keeps every constraint and increases no
completion time, so some optimal schedule has all `r n` start times below `r n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MPM OPEN SHOP OMPM2|chains;p_ij=1|ΣT_i is NP-complete.** Source: Timkovsky (2003), as
recorded in the Brucker-Knust classification (with the special case `O2|p_ij=1;chains|ΣT_i`);
Leung and Young (1990) (the case of one stage `{M_1}`); Brucker (2007), Chapter 10 (model). -/
public theorem_wanted mpmOpenShopTwoMachinesUnitChainsTotalTardiness_npComplete :
    mpmOpenShopTwoMachinesUnitChainsTotalTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mpmOpenShopTwoMachinesUnitChainsTotalTardinessDec

end MetaMathlibExt.Complexity.NPComplete.MPMOpenShopTwoMachinesUnitChainsTotalTardiness
