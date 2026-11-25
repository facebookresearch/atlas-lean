/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP WITH THREE JOBS (OMPM|n = 3|C_max) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (the MPM open-shop
model; Section 10.2: "Proceeding as for problem JMPM2|n = 3|C_max, FMPM|n = 3|C_max and
OMPM|n = 3|C_max can be shown to be NP-hard");
T. Gonzalez and S. Sahni, "Open shop scheduling to minimize finish time", Journal of the ACM 23
(1976), 665-679, doi:10.1145/321978.321985;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `OMPM|n = 3|C_max` as minimal NP-hard with the attribution to Gonzalez and
Sahni (1976).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopThreeJobsWanted
public import WantedExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopThreeJobs

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)
open MultipurposeFlowShopThreeJobs (MultipurposeFlowShopThreeJobsInstance Job Stage
  processingTime)

/-!
# MPM OPEN SHOP WITH THREE JOBS (OMPM|n = 3|C_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an MPM open shop with `r ≥ 1` stages and nonempty machine
sets `μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; exactly three jobs `J_1, J_2, J_3`, each
consisting of `r` operations `O_i1, …, O_ir` with processing times `p_ij ∈ ℤ₀⁺`; and a bound
`K`. QUESTION: is there a feasible schedule with makespan `max_i C_i ≤ K`?

Brucker, Chapter 10: "For the MPM flow shop problem, each job `J_i` has exactly `r` operations
`O_ij` (`j = 1, …, r`) and there is the same machine set `μ_j` associated with the `j`-th
operation of each job. [...] Furthermore, all machine sets are assumed to be different"; "MPM
open shop problems are defined like MPM flow shop problems. However, there are no precedence
constraints between the operations of an MPM open shop"; `O_ij` "has to be processed by one
machine in the set `μ_ij`". As in every open shop, the operations of a job may be processed in
any order but no two of them at the same time, and each machine processes at most one operation
at a time.

The instance type, the jobs, the stages, the processing times and the well-formedness of
`FMPM|n = 3|C_max` (`WantedExt.Complexity.NPComplete.MultipurposeFlowShopThreeJobsWanted`: the stage
machine sets name machines `< m`, there is at least one stage, and the sets are pairwise different;
exactly three jobs; every job lists one processing time per stage) are reused, and `WellFormed` adds
that every stage machine set is nonempty, as `MultipurposeFlowShopPrecedenceMakespan.WellFormed`
does. The completion time (the latest end `σ i s + p i s` of a job's operations) is
`MultipurposeFlowShopPrecedenceMakespan.completionTime`. A schedule is the MPM open-shop schedule
`MultipurposeOpenShopPrecedenceMakespan.IsMPMOpenShopSchedule` of `OMPM|prec; p_ij = 1|C_max`
(`MultipurposeOpenShopPrecedenceMakespanWanted`), which takes arbitrary processing times: each
operation `(i, s)` gets a start time `σ i s` and a machine `a i s ∈ μ_s`; two different operations
of the same job, and two different operations on the same machine, occupy disjoint time intervals
`[σ i s, σ i s + p i s)`. Classical open shops are the case `μ_s = {M_s}` (`r = m`); with three jobs
this is `O|n = 3|C_max`, which is `O3||C_max` with the roles of jobs and machines exchanged
(Gonzalez and Sahni prove `O3||C_max` NP-complete).

Numbers use the binary encoding. Membership in NP: start times can be taken at most the total
processing time, so `σ` and `a` are a polynomial certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: that of `FMPM|n = 3|C_max` (the machine environment is well
formed, exactly three jobs, one processing time per stage) and every stage machine set is
nonempty. -/
def WellFormed (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  MultipurposeFlowShopThreeJobs.WellFormed i ∧ ∀ M ∈ i.2.1, M ≠ []

/-- Some MPM open-shop schedule of the jobs has makespan at most `K`. -/
def MultipurposeOpenShopThreeJobsFeasible (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin i.1,
    IsMPMOpenShopSchedule i.1 i.2.1 (processingTime i) σ a ∧
      ∀ j, completionTime (processingTime i) σ j ≤ i.2.2.2

open Classical in
/-- `OMPM|n = 3|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeOpenShopThreeJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopThreeJobsInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeOpenShopThreeJobsFeasible i)
  | none => false

/-- **`OMPM|n = 3|C_max` is NP-complete.** Source: Brucker (2007), Section 10.2; Gonzalez and
Sahni (1976); Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted multipurposeOpenShopThreeJobs_npComplete :
    multipurposeOpenShopThreeJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeOpenShopThreeJobsDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopThreeJobs
