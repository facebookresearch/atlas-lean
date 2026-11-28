/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MPT OPEN SHOP, CHAINS, UNIT TIMES, TOTAL TARDINESS (OMPT2|chains; p_ij = 1|ΣT_i) is
NP-complete

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT2|chains; p_ij = 1|∑ T_i` as minimal NP-hard in the strong sense with
the attribution to Timkovsky (2003);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 11 (the MPT open-shop
model) and Section 1.3 (precedence relations).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsTardiness

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open UnitFlowShopPrecedenceMakespan (UnitJobs)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopPrecedenceSchedule)
open F3UnitChainsLateJobs (ChainsWellFormed)

/-!
# TWO-MACHINE MPT OPEN SHOP, CHAINS, UNIT TIMES, TOTAL TARDINESS (OMPT2|chains; p_ij = 1|ΣT_i)
is NP-complete

INSTANCE: two machines `M_1, M_2`; an open shop with multiprocessor tasks (MPT) with `r ≥ 1`
stages and machine sets `μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `1, …, n`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij`
requires every machine of `μ_j` during its processing and the operations of a job may be
processed in any order, but no two of them at the same time; a due date `d_i ∈ ℤ₀⁺` for each job
`i`; a precedence relation `→` on the jobs consisting of disjoint chains (each job has at most
one immediate predecessor and at most one immediate successor), where `i → k` means that no
operation of `k` starts before every operation of `i` is completed; and a bound `K`. Operations
requiring a common machine cannot be processed simultaneously. QUESTION: is there a feasible
schedule whose total tardiness `∑_i max(0, C_i - d_i)` is at most `K`, where `C_i` is the
completion time of job `i` (that of its last operation)?

The MPT open shop is that of `MultiprocessorTaskOpenShopPrecedenceMakespanWanted`
(`OMPT|prec; p_ij = 1|C_max`), reused here: the stage machine sets and their well-formedness
`StagesWellFormed` (at least one stage, machine indices below `m`, pairwise different sets), the
unit-job condition `UnitJobs`, the unit-time open-shop schedule with precedence
`IsMPTOpenShopPrecedenceSchedule` and the completion time `completionTime`. The number of
machines is fixed to `m = 2`. The chains are given by their arcs `(i, k)` (`i` the immediate
predecessor of `k`), with the chain condition `ChainsWellFormed` of `F3UnitChainsLateJobsWanted`
(distinct arcs naming jobs, at most one immediate successor and one immediate predecessor per
job, no cycle). Each job is listed with its processing times `(p_i1, …, p_ir)`, all equal to `1`,
and its due date. With integer data, integer start times lose no generality. Binary encoding of
all numbers (the problem is NP-complete in the strong sense).

Brucker and Knust's open-shop table lists `O2|p_ij = 1; chains|∑ T_i` as strongly NP-hard
(Timkovsky 2003, whose paper was not available to this formalization); it is the special case
`r = 2`, `μ_1 = {M_1}`, `μ_2 = {M_2}` of this problem.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`OMPT2|chains; p_ij = 1|∑ T_i` is NP-complete.** Source: Timkovsky (2003); Brucker and
Knust, *Complexity results for scheduling problems*; Brucker (2004), Chapter 11. -/
public theorem_wanted multiprocessorTaskOpenShopChainsTardiness_npComplete :
    multiprocessorTaskOpenShopChainsTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskOpenShopChainsTardinessDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsTardiness
