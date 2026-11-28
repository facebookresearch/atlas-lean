/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP WITH THREE JOBS (OMPM|n = 3|C_max): definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopThreeJobsDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopThreeJobs

open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)
open MultipurposeFlowShopThreeJobs (MultipurposeFlowShopThreeJobsInstance Job Stage
  processingTime)

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

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopThreeJobs
