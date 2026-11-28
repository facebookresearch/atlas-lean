/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM|r_i;p_ij=1|ΣU_i is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Shop problems with multipurpose machines" (`OMPM|p_ij=1;r_i|ΣU_i`, minimal NP-hard in the
strong sense, credited to Kravchenko 1999);
S. A. Kravchenko, "On the complexity of minimizing the number of late jobs in unit time open
shop", Discrete Applied Mathematics 100 (2000), 127-132, doi:10.1016/S0166-218X(99)00202-4 (the
open shop `O|p_ij=1;r_i|ΣU_i`, the case `μ_j = {M_j}`; the full text was not available);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM open-shop
model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeUnitOpenShopReleaseLateJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeUnitOpenShopReleaseLateJobs

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeFlowShopThreeJobs (Job Stage processingTime)
open MultipurposeOpenShopMakespan (MultipurposeOpenShopMakespanInstance)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)

/-!
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM|r_i;p_ij=1|ΣU_i is NP-complete

INSTANCE: machines `M_1, …, M_m`; an MPM open shop with `r ≥ 1` stages and nonempty machine sets
`μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij = 1`, where `O_ij` is processed by one
machine of `μ_j`, and the operations of a job are processed in any order but no two of them at
the same time; a release date `r_i ∈ ℤ₀⁺` for each job, before which none of its operations
starts; a due date `d_i ∈ ℤ₀⁺` for each job; and a bound `K`. Each machine processes at most one
operation at a time. QUESTION: is there a feasible schedule with at most `K` late jobs, i.e. jobs
`i` with `C_i > d_i`, where `C_i` is the completion time of job `i` (that of its last
operation)?

This is Brucker and Knust's `OMPM|p_ij=1;r_i|ΣU_i`, which they classify as NP-hard in the strong
sense, citing Kravchenko (1999) for the open shop `O|p_ij=1;r_i|ΣU_i`
(`UnitOpenShopReleaseLateJobsWanted`), the case `r = m`, `μ_j = {M_j}`. It is `OMPM||C_max`
(`MultipurposeOpenShopMakespanWanted`) with unit processing times, release dates, due dates, and
the number of late jobs in place of the makespan: the instance pairs that module's instance (`m`,
the machine sets, one list of processing times per job, and a bound, here `K`) with the pairs
`(r_i, d_i)`, one per job, and `WellFormed` is that module's well-formedness plus unit processing
times and one pair per job. The schedule is `IsMPMOpenShopSchedule`
(`MultipurposeOpenShopPrecedenceMakespanWanted`) plus `r_i ≤ σ i s` for every operation `(i, s)`;
`C_i` is `completionTime` (`MultipurposeFlowShopPrecedenceMakespanWanted`). Binary encoding of
all numbers. Membership in NP: the machines and start times (each below `max_i r_i + n · r`
without loss of generality) are a certificate checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`OMPM|p_ij=1;r_i|ΣU_i` is NP-complete.** Source: Brucker and Knust's classification;
Kravchenko (2000). -/
public theorem_wanted multipurposeUnitOpenShopReleaseLateJobs_npComplete :
    multipurposeUnitOpenShopReleaseLateJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeUnitOpenShopReleaseLateJobsDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeUnitOpenShopReleaseLateJobs
