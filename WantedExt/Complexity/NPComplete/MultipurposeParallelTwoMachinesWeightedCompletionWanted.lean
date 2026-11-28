/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING (PMPM2||Σw_iC_i) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE
WEIGHTED COMPLETION TIME (comment: remains NP-complete for `m = 2`);
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X;
J. Bruno, E. G. Coffman, Jr. and R. Sethi, "Scheduling independent tasks to reduce mean
finishing time", Communications of the ACM 17 (1974), 382-387, doi:10.1145/361011.361064;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Multipurpose
machine problems" (`PMPM2||Σw_iC_i`, minimal NP-hard, credited to Bruno et al. (1974)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesWeightedCompletion

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule)

/-!
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING (PMPM2||Σw_iC_i) is NP-complete

INSTANCE: `m = 2` identical parallel machines `M₁, M₂`; jobs `1, …, n`, each with a processing
time `pᵢ ∈ ℤ₀⁺`, a nonempty set `μᵢ ⊆ {M₁, M₂}` of eligible machines and a weight `wᵢ ∈ ℤ₀⁺`;
and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a nonpreemptive schedule, every job processed on
exactly one machine of its set and each machine processing at most one job at a time, whose
total weighted completion time `Σᵢ wᵢCᵢ` is at most `K`, where `Cᵢ` is the completion time of
job `i`?

With every `μᵢ = {M₁, M₂}` the problem is `P2||Σw_iC_i`
(`TwoProcessorWeightedCompletionTimeWanted`), SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME
with two processors ([SS13], which "remains NP-complete for `m = 2`", referencing Lenstra,
Rinnooy Kan and Brucker). Brucker and Knust list `PMPM2||Σw_iC_i` as minimal NP-hard (in the
ordinary sense), crediting Bruno, Coffman and Sethi, whose abstract states that "the most general
mean-finishing-time problem for independent tasks is polynomial complete".

The machines, jobs and machine sets are those of `PMPM2||C_max`
(`MultipurposeParallelTwoMachinesMakespanWanted`, Brucker's multi-purpose machine model of
*Scheduling Algorithms*, Chapter 10): an instance is an MPM job-shop instance with `m = 2` in
which every job is one operation `(pᵢ, μᵢ)`, its bound component being `K`, together with the
weights, one per job, listed in job order; `WellFormed` is that module's well-formedness
(machine sets nonempty and in `{1, 2}`, single-operation jobs) plus one weight per job. A
schedule is an MPM schedule (`MultiPurposeJobShopThreeJobs.IsMPMJobShopSchedule`) as in that
module, and `Cᵢ = σᵢ + pᵢ`. Every job has exactly one operation, so the total weighted
completion time is the sum over the operations `t` of `w_j · (σ t + p_t)` for the job `j` of
`t`. Processing times and weights are nonnegative; the positive lengths and weights of [SS13]
are a special case. Integral start times lose no generality, since the data are integers.
Membership in NP: the machines, in `{1, 2}`, and the start times are a certificate; shifting the
jobs on each machine left to remove idle time keeps the machine assignment and increases no
completion time, so some optimal schedule has every start time at most `Σᵢ pᵢ`, and the
certificate has polynomial size. Binary encoding of all numbers (for fixed `m` the problem
is solvable in pseudo-polynomial time, so it is NP-complete only in the ordinary sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`PMPM2||Σw_iC_i` is NP-complete.** Source: Garey and Johnson (1979), [SS13] (`m = 2`), and
Lenstra, Rinnooy Kan and Brucker (1977), via the case `μᵢ = {M₁, M₂}`; Bruno, Coffman and Sethi
(1974), as recorded in Brucker and Knust's classification; Brucker (2007), Chapter 10. -/
public theorem_wanted multipurposeParallelTwoMachinesWeightedCompletion_npComplete :
    multipurposeParallelTwoMachinesWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelTwoMachinesWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesWeightedCompletion
