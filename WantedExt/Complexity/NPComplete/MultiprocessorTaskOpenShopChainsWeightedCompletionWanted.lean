/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MPT OPEN SHOP, CHAINS, UNIT TIMES, WEIGHTED COMPLETION TIME
(OMPT2|chains; p_ij = 1|Σw_iC_i) is NP-complete

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149(2) (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT2|chains; p_ij = 1|Σw_iC_i` as minimal NP-hard in the strong sense
with the attribution to Timkovsky (2003);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 11 (the MPT open-shop
model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsWeightedCompletion

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopPrecedenceSchedule)
open MultiprocessorTaskOpenShopChainsTardiness (MultiprocessorTaskOpenShopChainsTardinessInstance)

/-!
# TWO-MACHINE MPT OPEN SHOP, CHAINS, UNIT TIMES, WEIGHTED COMPLETION TIME
(OMPT2|chains; p_ij = 1|Σw_iC_i) is NP-complete

INSTANCE: two machines `M_1, M_2`; an open shop with multiprocessor tasks (MPT) with `r ≥ 1` stages
and machine sets `μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `1, …, n` with `n ≥ 1`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij` requires
every machine of `μ_j` during its processing and the operations of a job may be processed in any
order, but no two of them at the same time; a weight `w_i ∈ ℤ₀⁺` for each job `i`; a precedence
relation `→` on the jobs consisting of disjoint chains (each job has at most one immediate
predecessor and at most one immediate successor), where `i → k` means that no operation of `k`
starts before every operation of `i` is completed; and a bound `K`. Operations requiring a common
machine cannot be processed simultaneously. QUESTION: is there a feasible schedule with total
weighted completion time `Σ_i w_i C_i ≤ K`, where `C_i` is the completion time of job `i` (that of
its last operation)?

The instance and its well-formedness (plus `n ≥ 1`: there is at least one job) are those of
`OMPT2|chains; p_ij = 1|ΣT_i` (`MultiprocessorTaskOpenShopChainsTardinessWanted`): the number of
machines, fixed to `m = 2`; the stage machine sets; the jobs, each listed with its processing times
`(p_i1, …, p_ir)`, all equal to `1`, and one number, here its weight `w_i` (`weight`; the due date
there); the chain arcs `(i, k)` (`i` the immediate predecessor of `k`); and `K`. The unit-time MPT
open-shop schedule with precedence `IsMPTOpenShopPrecedenceSchedule` and the completion time
`completionTime` are those of `OMPT|prec; p_ij = 1|C_max`
(`MultiprocessorTaskOpenShopPrecedenceMakespanWanted`), after Brucker's MPT model (*Scheduling
Algorithms*, Chapter 11). Only the objective differs: the total weighted completion time instead of
the total tardiness.

Brucker and Knust record `OMPT2|chains; p_ij = 1|Σw_iC_i` as minimal NP-hard in the strong
sense with the attribution to Timkovsky (2003); the classical two-machine open shop
`O2|p_ij = 1; chains|Σw_iC_i` is its special case `r = 2`, `μ_1 = {M_1}`, `μ_2 = {M_2}`. NP
membership: removing a unit time slot in which no operation runs delays no job, so a schedule
with `Σ_i w_i C_i ≤ K` exists if and only if one exists with all start times below `r · n`;
such start times are a certificate of polynomial size, checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`OMPT2|chains; p_ij = 1|Σw_iC_i` is NP-complete.** Source: Timkovsky (2003); Brucker and
Knust, *Complexity results for scheduling problems*; Brucker (2007), Chapter 11. -/
public theorem_wanted multiprocessorTaskOpenShopChainsWeightedCompletion_npComplete :
    multiprocessorTaskOpenShopChainsWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiprocessorTaskOpenShopChainsWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopChainsWeightedCompletion
