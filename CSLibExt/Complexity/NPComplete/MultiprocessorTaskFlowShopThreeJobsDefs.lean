/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT FLOW SHOP WITH THREE JOBS (FMPT|n = 3|C_max): definitions

Source:
A. Krämer, *Scheduling Multiprocessor Tasks on Dedicated Processors*, PhD thesis, Universität
Osnabrück, Fachbereich Mathematik/Informatik (1995);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 11 (the MPT flow-shop model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `FMPT|n = 3|C_max` as minimal NP-hard (in the ordinary sense), citing Krämer
(1995).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopPrecedenceMakespanDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopThreeJobs

open MultipurposeFlowShopThreeJobs
  (MultipurposeFlowShopThreeJobsInstance Job Stage processingTime)
open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultiprocessorTaskFlowShopPrecedenceMakespan (IsMPTFlowShopSchedule)

/-- Well-formedness of an instance: a well-formed `FMPM|n = 3|C_max` instance (at least one stage,
machine indices below `m`, pairwise different sets, exactly three jobs, one processing time per
stage) whose machine sets are all nonempty. -/
def WellFormed (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  MultipurposeFlowShopThreeJobs.WellFormed i ∧ ∀ M ∈ i.2.1, M ≠ []

/-- Some MPT flow-shop schedule of the three jobs has makespan at most `K`. -/
def MultiprocessorTaskFlowShopThreeJobsFeasible (i : MultipurposeFlowShopThreeJobsInstance) :
    Prop :=
  ∃ σ : Job i → Stage i → ℕ, IsMPTFlowShopSchedule i.2.1 (processingTime i) σ ∧
    ∀ j, completionTime (processingTime i) σ j ≤ i.2.2.2

open Classical in
/-- `FMPT|n = 3|C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskFlowShopThreeJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopThreeJobsInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskFlowShopThreeJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskFlowShopThreeJobs
