/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM||Cmax is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM open-shop
model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Shop problems with multipurpose machines" (`OMPM||C_max`, minimal NP-hard in the strong
sense, credited to an unpublished result of J. K. Lenstra);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING (the case
`μ_j = {M_j}`; comment: "NP-complete in the strong sense for m arbitrary [Lenstra, 1977]");
T. Gonzalez and S. Sahni, "Open shop scheduling to minimize finish time", Journal of the ACM 23
(1976), 665-679, doi:10.1145/321978.321985.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopMakespan

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeFlowShopThreeJobs (MultipurposeFlowShopThreeJobsInstance Job Stage processingTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)

/-!
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM||Cmax is NP-complete

INSTANCE: machines `M_1, …, M_m` (`m` part of the input); an MPM open shop with `r ≥ 1` stages and
nonempty machine sets `μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `J_1, …, J_n`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij ∈ ℤ₀⁺`, where `O_ij` is
processed by one machine of `μ_j`, and the operations of a job are processed in any order but no
two of them at the same time; and a bound `K`. Each machine processes at most one operation at a
time. QUESTION: is there a feasible schedule with makespan `max_i C_i ≤ K`, where `C_i` is the
completion time of job `i` (that of its last operation)?

This is Brucker and Knust's `OMPM||C_max`, which they classify as NP-hard in the strong sense,
crediting an unpublished result of Lenstra. It contains OPEN-SHOP SCHEDULING ([SS14],
`OpenShopSchedulingWanted`) as the case `r = m`, `μ_j = {M_j}`; Garey and Johnson record that case
as NP-complete for `m = 3` (Gonzalez and Sahni 1976) and in the strong sense for arbitrary `m`
(Lenstra 1977). The MPM open shop is Brucker's (Chapter 10), as stated in
`MultipurposeOpenShopPrecedenceMakespanWanted`: the schedule is that module's
`IsMPMOpenShopSchedule` (operation `(i, s)` gets a start time `σ i s` and a machine `a i s ∈ μ_s`;
two operations of one job, and two operations on one machine, occupy disjoint intervals
`[σ i s, σ i s + p_is)`), and `completionTime` (the latest completion of a job's operations) is
that of `MultipurposeFlowShopPrecedenceMakespanWanted`. The instance type
(`m`, `[μ_1, …, μ_r]`, one list `[p_i1, …, p_ir]` of processing times per job, `K`), the jobs, the
stages and `processingTime` are those of `MultipurposeFlowShopThreeJobsWanted` (`FMPM|n = 3|C_max`,
whose data are the same; the type is exposed here as `MultipurposeOpenShopMakespanInstance`);
`WellFormed` is that module's well-formedness without its condition
`n = 3`, with nonempty machine sets as in `MultipurposeOpenShopPrecedenceMakespanWanted`. With
integer data, integer start times lose no generality. Binary encoding of all numbers. Membership
in NP: the machines and start times (each at most `K`) are a certificate checked in polynomial
time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`OMPM||C_max` is NP-complete.** Source: Brucker and Knust's classification (Lenstra,
unpublished); Garey and Johnson (1979), [SS14]; Gonzalez and Sahni (1976). -/
public theorem_wanted multipurposeOpenShopMakespan_npComplete :
    multipurposeOpenShopMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeOpenShopMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopMakespan
