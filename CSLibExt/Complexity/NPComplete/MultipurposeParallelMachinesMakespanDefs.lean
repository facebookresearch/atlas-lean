/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPURPOSE-MACHINE SCHEDULING (PMPM||Cmax): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS8] MULTIPROCESSOR SCHEDULING
(comment: "NP-complete in the strong sense for `m` arbitrary (3-PARTITION is a special case)");
M. R. Garey and D. S. Johnson, ""Strong" NP-completeness results: motivation, examples, and
implications", Journal of the ACM 25 (1978), 499-508, doi:10.1145/322077.322090;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Multipurpose
machine problems" (`PMPM||C_max`, minimal NP-hard in the strong sense, credited to Garey and
Johnson (1978)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelMachinesMakespan

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance MPMWellFormed)
open MultipurposeParallelTwoMachinesMakespan (MultipurposeParallelTwoMachinesMakespanFeasible)

/-- Well-formedness of an instance: a well-formed MPM job-shop instance whose number `m` of
machines is positive (nonempty machine sets in `{1, …, m}`) and in which every job has exactly
one operation. -/
def WellFormed (i : MPMJobShopInstance) : Prop :=
  MPMWellFormed i.1 i ∧ 0 < i.1 ∧ ∀ job ∈ i.2.1, job.length = 1

open Classical in
/-- `PMPM||C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelMachinesMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMJobShopInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeParallelTwoMachinesMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelMachinesMakespan
