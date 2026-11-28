/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP WITH TWO PROCESSORS, TOTAL COMPLETION TIME (OMPT2||ΣC_i): definitions

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 11 (multiprocessor
tasks: the MPT open-shop model);
J. O. Achugbue and F. Y. Chin, "Scheduling the open shop to minimize mean flow time", SIAM
Journal on Computing 11(4) (1982), 709-720, doi:10.1137/0211058;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT2||ΣC_i` as minimal NP-hard in the strong sense with the attribution
to Achugbue and Chin (1982).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopThreeJobsDefs
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesTotalCompletion

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed completionTime)
open MultipurposeFlowShopThreeJobs (MultipurposeFlowShopThreeJobsInstance Job Stage
  processingTime)
open MultiprocessorTaskOpenShopPrecedenceMakespan (IsMPTOpenShopSchedule)

/-- Well-formedness of an instance: there are two processors (`m = 2`), the stage processor sets
are well formed (`StagesWellFormed`), every job lists one processing time per stage, and there is
at least one job (as in `TwoProcessorOpenShopMeanFlowTimeWanted`). -/
def WellFormed (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  i.1 = 2 ∧ StagesWellFormed i.1 i.2.1 ∧ (∀ job ∈ i.2.2.1, job.length = i.2.1.length) ∧
    0 < i.2.2.1.length

/-- Some MPT open-shop schedule of the jobs has total completion time at most `K`. -/
def MultiprocessorTaskOpenShopTwoMachinesTotalCompletionFeasible
    (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, IsMPTOpenShopSchedule i.2.1 (processingTime i) σ ∧
    ∑ j, completionTime (processingTime i) σ j ≤ i.2.2.2

open Classical in
/-- `OMPT2||ΣC_i` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopTwoMachinesTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopThreeJobsInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultiprocessorTaskOpenShopTwoMachinesTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopTwoMachinesTotalCompletion
