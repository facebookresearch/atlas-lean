/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP WITH THREE PROCESSORS (OMPT3||C_max): definitions

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 11 (multiprocessor
tasks: the MPT open-shop model);
T. Gonzalez and S. Sahni, "Open shop scheduling to minimize finish time", Journal of the ACM
23(4) (1976), 665-679, doi:10.1145/321978.321985;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT3||C_max` as minimal NP-hard (in the ordinary sense) with the
attribution to Gonzalez and Sahni (1976).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopThreeJobsDefs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopThreeMachines

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeFlowShopThreeJobs (MultipurposeFlowShopThreeJobsInstance Job Stage
  processingTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopSchedule)

/-- Well-formedness of an instance: there are three processors (`m = 3`), the stage processor
sets are well formed (`StagesWellFormed`), and every job lists one processing time per stage. -/
def WellFormed (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  i.1 = 3 ∧ StagesWellFormed i.1 i.2.1 ∧ ∀ job ∈ i.2.2.1, job.length = i.2.1.length

/-- Some MPT open-shop schedule of the jobs has makespan at most `K`. -/
def MultiprocessorTaskOpenShopThreeMachinesFeasible
    (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, IsMPTOpenShopSchedule i.2.1 (processingTime i) σ ∧
    ∀ j, completionTime (processingTime i) σ j ≤ i.2.2.2

open Classical in
/-- `OMPT3||C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopThreeMachinesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopThreeJobsInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskOpenShopThreeMachinesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopThreeMachines
