/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE MULTIPURPOSE-MACHINE SCHEDULING (PMPM2||Σw_iC_i): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE
WEIGHTED COMPLETION TIME (comment: remains NP-complete for `m = 2`);
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X;
J. Bruno, E. G. Coffman, Jr. and R. Sethi, "Scheduling independent tasks to reduce mean
finishing time", Communications of the ACM 17 (1974), 382-387, doi:10.1145/361011.361064;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 10 (multi-purpose
machines);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Multipurpose
machine problems" (`PMPM2||Σw_iC_i`, minimal NP-hard, credited to Bruno et al. (1974)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesWeightedCompletion

open MultiPurposeJobShopThreeJobs (MPMJobShopInstance Operation opLength IsMPMJobShopSchedule)

/-- An instance: a `PMPM2||C_max` instance (the MPM job-shop instance, whose bound component is
`K`) and the weights, job `j` having the `j`-th listed weight `w_j`. -/
abbrev MultipurposeParallelTwoMachinesWeightedCompletionInstance := MPMJobShopInstance × List ℕ

/-- The weight `w_j` of job `j`. -/
def weight (i : MultipurposeParallelTwoMachinesWeightedCompletionInstance)
    (j : Fin i.1.2.1.length) : ℕ :=
  i.2.getD j 0

/-- Well-formedness of an instance: a well-formed `PMPM2||C_max` instance (two machines,
nonempty machine sets in `{1, 2}`, single-operation jobs) and one weight per job. -/
def WellFormed (i : MultipurposeParallelTwoMachinesWeightedCompletionInstance) : Prop :=
  MultipurposeParallelTwoMachinesMakespan.WellFormed i.1 ∧ i.2.length = i.1.2.1.length

/-- Some MPM schedule of the jobs has total weighted completion time at most `K`: the sum, over
the operations `t` (one per job), of `w_j · (σ t + p_t)` for the job `j` of `t`. -/
def MultipurposeParallelTwoMachinesWeightedCompletionFeasible
    (i : MultipurposeParallelTwoMachinesWeightedCompletionInstance) : Prop :=
  ∃ a σ : Operation i.1 → ℕ, IsMPMJobShopSchedule i.1 a σ ∧
    (∑ t : Operation i.1, weight i t.1 * (σ t + opLength i.1 t)) ≤ i.1.2.2

open Classical in
/-- `PMPM2||Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def multipurposeParallelTwoMachinesWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeParallelTwoMachinesWeightedCompletionInstance) x with
  | some i =>
    decide (WellFormed i ∧ MultipurposeParallelTwoMachinesWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelTwoMachinesWeightedCompletion
