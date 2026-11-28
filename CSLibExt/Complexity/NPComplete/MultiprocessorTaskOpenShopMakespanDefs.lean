/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPT OPEN SHOP (OMPT||C_max): definitions

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 11 (multiprocessor
tasks: the MPT open-shop model);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING, p. 241
(comment: "NP-complete in the strong sense for m arbitrary [Lenstra, 1977]", a private
communication; the original was not available);
D. P. Williamson, L. A. Hall, J. A. Hoogeveen, C. A. J. Hurkens, J. K. Lenstra,
S. V. Sevast'janov and D. B. Shmoys, "Short shop schedules", Operations Research 45 (1997),
288-294, doi:10.1287/opre.45.2.288;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multiprocessor
tasks", which lists `OMPT||C_max` as minimal NP-hard (strongly), crediting an unpublished
result of J. K. Lenstra.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopThreeMachinesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopMakespan

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed)
open MultipurposeFlowShopThreeJobs (MultipurposeFlowShopThreeJobsInstance)
open MultiprocessorTaskOpenShopThreeMachines (MultiprocessorTaskOpenShopThreeMachinesFeasible)

/-- Well-formedness of an instance: at least one processor (`m ≥ 1`), well-formed stage
processor sets (`StagesWellFormed`), and one processing time per stage for every job. -/
def WellFormed (i : MultipurposeFlowShopThreeJobsInstance) : Prop :=
  0 < i.1 ∧ StagesWellFormed i.1 i.2.1 ∧ ∀ job ∈ i.2.2.1, job.length = i.2.1.length

open Classical in
/-- `OMPT||C_max` as a decision problem over bitstrings. -/
noncomputable def multiprocessorTaskOpenShopMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopThreeJobsInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorTaskOpenShopThreeMachinesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorTaskOpenShopMakespan
