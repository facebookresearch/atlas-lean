/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH UNIT-TIME CHAINS (PMPM2|chains;p_i=1|Σw_iC_i)
is NP-complete

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8 (the full
texts of both papers were not available);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Parallel machine
problems without preemption" (`P2|p_i=1;chains|Σw_iC_i`, minimal NP-hard in the strong sense,
credited to Timkovsky (2003)) and class "Multipurpose machine problems"
(`PMPM2|chains;p_i=1|Σw_iC_i`, minimal NP-hard in the strong sense, credited to Timkovsky
(1998));
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MPMParallelTwoMachinesUnitChainsWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMParallelTwoMachinesUnitChainsWeightedCompletion

open MultiPurposeJobShopThreeJobs (Operation opLength IsMPMJobShopSchedule)
open UnitFlowShopPrecedenceMakespan (Prec)
open MultipurposeParallelTwoMachinesUnitChainsMakespan
  (MultipurposeParallelTwoMachinesUnitChainsMakespanInstance)

/-!
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING WITH UNIT-TIME CHAINS (PMPM2|chains;p_i=1|Σw_iC_i)
is NP-complete

INSTANCE: `m = 2` identical parallel machines; jobs `1, …, n`, each with processing time
`pᵢ = 1`, a nonempty set `μᵢ ⊆ {M₁, M₂}` of eligible machines and a weight `wᵢ ∈ ℤ₀⁺`;
precedence constraints that form a set of chains (every job has at most one immediate
predecessor and at most one immediate successor), where `i` preceding `j` means that `j` cannot
start before `i` is completed; and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a schedule, every job on
one machine of its set, whose total weighted completion time `Σᵢ wᵢCᵢ` is at most `K`, where `Cᵢ`
is the completion time of job `i`?

With every `μᵢ = {M₁, M₂}` the problem is `P2|chains;p_i=1|Σw_iC_i`
(`TwoProcessorUnitChainsWeightedCompletionWanted`), which Brucker and Knust list as minimal
NP-hard in the strong sense in their table of parallel machine problems, crediting Timkovsky
(2003); they list `PMPM2|chains;p_i=1|Σw_iC_i` as minimal NP-hard in the strong sense in their
table of multipurpose machine problems, crediting Timkovsky (1998). The full texts of both papers
were not available.

The machines, jobs, machine sets and chains are those of `PMPM2|chains; p_i=1|C_max`
(`MultipurposeParallelTwoMachinesUnitChainsMakespanWanted`, Brucker's multi-purpose machine model
of *Scheduling Algorithms*, Chapter 10): an instance is that module's instance (an MPM job-shop
instance with `m = 2` in which every job is one unit operation, its bound component being `K`,
together with the precedence arcs, job `i` preceding job `k` when `k` is reachable from `i` along
arcs) and the weights, one per job, listed in job order; `WellFormed` is that module's
well-formedness (machine sets nonempty and in `{1, 2}`, unit single-operation jobs, acyclic arcs
naming jobs that form chains) plus one weight per job. A schedule is an MPM schedule
(`MultiPurposeJobShopThreeJobs.IsMPMJobShopSchedule`) obeying the arcs, as in that module, and
`Cᵢ = σᵢ + 1`. Every job has exactly one operation, so the total weighted completion time is the
sum over the operations `t` of `w_j · (σ t + p_t)` for the job `j` of `t`. Integral start times
lose no generality, since the data are integers; membership in NP holds because removing a time
slot in which no job runs keeps a schedule feasible and increases no completion time, so a
schedule meeting `K` can be taken with all start times below `n`. Binary encoding of all numbers
(the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`PMPM2|chains; p_i=1|Σw_iC_i` is NP-complete.** Source: Timkovsky (2003), via the case
`μᵢ = {M₁, M₂}`, and Timkovsky (1998), as recorded in Brucker and Knust's classification;
Brucker (2007), Chapter 10. -/
public theorem_wanted mpmParallelTwoMachinesUnitChainsWeightedCompletion_npComplete :
    mpmParallelTwoMachinesUnitChainsWeightedCompletionDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L
            mpmParallelTwoMachinesUnitChainsWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MPMParallelTwoMachinesUnitChainsWeightedCompletion
