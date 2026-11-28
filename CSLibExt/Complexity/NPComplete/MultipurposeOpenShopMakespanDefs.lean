/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE OPEN SHOP OMPM||Cmax: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopThreeJobsDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopMakespan

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeFlowShopThreeJobs (MultipurposeFlowShopThreeJobsInstance Job Stage processingTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)

/-- An instance: the number of machines `m`, the stage machine sets `[μ_1, …, μ_r]`, one list
`[p_i1, …, p_ir]` of processing times per job (any number of jobs), and the bound `K` (the
instance type of `MultipurposeFlowShopThreeJobsWanted`). -/
abbrev MultipurposeOpenShopMakespanInstance := MultipurposeFlowShopThreeJobsInstance

/-- Well-formedness of an instance: the machine environment is well formed (`StagesWellFormed`:
at least one stage, machine indices below `m`, pairwise different machine sets), every machine
set is nonempty, and every job lists one processing time per stage. -/
def WellFormed (i : MultipurposeOpenShopMakespanInstance) : Prop :=
  StagesWellFormed i.1 i.2.1 ∧ (∀ M ∈ i.2.1, M ≠ []) ∧
    ∀ job ∈ i.2.2.1, job.length = i.2.1.length

/-- Some MPM open-shop schedule of the jobs has makespan at most `K`. -/
def MultipurposeOpenShopMakespanFeasible (i : MultipurposeOpenShopMakespanInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin i.1,
    IsMPMOpenShopSchedule i.1 i.2.1 (processingTime i) σ a ∧
      ∀ j, completionTime (processingTime i) σ j ≤ i.2.2.2

open Classical in
/-- `OMPM||C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeOpenShopMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeOpenShopMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeOpenShopMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeOpenShopMakespan
