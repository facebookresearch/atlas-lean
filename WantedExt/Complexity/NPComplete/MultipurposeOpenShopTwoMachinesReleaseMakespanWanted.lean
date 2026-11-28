/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM2|r_i|Cmax is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Shop problems with multipurpose machines" (`OMPM2|r_i|C_max`, minimal NP-hard in the strong
sense, credited to Lawler, Lenstra, and Rinnooy Kan 1981, 1982);
E. L. Lawler, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Minimizing maximum lateness in a
two-machine open shop", Mathematics of Operations Research 6 (1981), 153-158,
doi:10.1287/moor.6.1.153; Erratum, Mathematics of Operations Research 7 (1982), 635,
doi:10.1287/moor.7.4.635 (the two-machine open shop, the case `μ_j = {M_j}`);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM open-shop
model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesReleaseMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesReleaseMakespan

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeFlowShopThreeJobs (Job Stage processingTime)
open MultipurposeOpenShopMakespan (MultipurposeOpenShopMakespanInstance)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)

/-!
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM2|r_i|Cmax is NP-complete

INSTANCE: two machines `M_1, M_2`; an MPM open shop with `r ≥ 1` stages and nonempty machine sets
`μ_1, …, μ_r ⊆ {M_1, M_2}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij ∈ ℤ₀⁺`, where `O_ij` is processed by one
machine of `μ_j`, and the operations of a job are processed in any order but no two of them at
the same time; a release date `r_i ∈ ℤ₀⁺` for each job, before which none of its operations
starts; and a bound `K`. Each machine processes at most one operation at a time. QUESTION: is
there a feasible schedule with makespan `max_i C_i ≤ K`, where `C_i` is the completion time of
job `i` (that of its last operation)?

This is Brucker and Knust's `OMPM2|r_i|C_max`, which they classify as NP-hard in the strong
sense, citing Lawler, Lenstra, and Rinnooy Kan (1981, with their 1982 erratum), whose
two-machine open shop `O2|r_i|C_max` is the case `r = 2`, `μ_1 = {M_1}`, `μ_2 = {M_2}`. It is
`OMPM||C_max` (`MultipurposeOpenShopMakespanWanted`) with `m = 2` and release dates: the instance
pairs that module's instance (`m`, the machine sets, one list of processing times per job, `K`)
with the list of release dates, and `WellFormed` is that module's well-formedness plus `m = 2`
and one release date per job. The schedule is `IsMPMOpenShopSchedule`
(`MultipurposeOpenShopPrecedenceMakespanWanted`) with the makespan bound through `completionTime`
(`MultipurposeFlowShopPrecedenceMakespanWanted`), as in `OMPM||C_max`, plus `r_i ≤ σ i s` for
every operation `(i, s)`. Binary encoding of all numbers. Membership in NP: the machines and
start times (each at most `K`) are a certificate checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`OMPM2|r_i|C_max` is NP-complete.** Source: Brucker and Knust's classification; Lawler,
Lenstra, and Rinnooy Kan (1981; erratum 1982). -/
public theorem_wanted multipurposeOpenShopTwoMachinesReleaseMakespan_npComplete :
    multipurposeOpenShopTwoMachinesReleaseMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeOpenShopTwoMachinesReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopTwoMachinesReleaseMakespan
