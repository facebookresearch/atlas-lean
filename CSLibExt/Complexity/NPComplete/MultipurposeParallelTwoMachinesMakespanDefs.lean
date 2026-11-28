/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING (PMPM2||Cmax): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS8] MULTIPROCESSOR SCHEDULING
(comment: remains NP-complete for `m = 2`);
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Multipurpose
machine problems" (`PMPM2||C_max`, minimal NP-hard, credited to Lenstra et al. (1977)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiPurposeJobShopThreeJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesMakespan

open MultiPurposeJobShopThreeJobs
  (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule MPMWellFormed)

/-- Well-formedness of an instance: a well-formed MPM job-shop instance with `m = 2` machines
(nonempty machine sets in `{1, 2}`) in which every job has exactly one operation. -/
def WellFormed (i : MPMJobShopInstance) : Prop :=
  MPMWellFormed 2 i ∧ ∀ job ∈ i.2.1, job.length = 1

/-- Some MPM schedule of the jobs completes every job by `K`. -/
def MultipurposeParallelTwoMachinesMakespanFeasible (i : MPMJobShopInstance) : Prop :=
  ∃ a σ : Operation i → ℕ, IsMPMJobShopSchedule i a σ ∧ ∀ t, σ t + opLength i t ≤ i.2.2

open Classical in
/-- `PMPM2||C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelTwoMachinesMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMJobShopInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeParallelTwoMachinesMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesMakespan
