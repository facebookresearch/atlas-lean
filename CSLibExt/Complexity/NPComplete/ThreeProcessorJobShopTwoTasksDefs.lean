/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR JOB-SHOP SCHEDULING with at most two tasks per job: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 242, problem [SS18] JOB-SHOP
SCHEDULING, comment: "NP-complete (in the ordinary sense) if ... `m = 3` and `n_j ≤ 2` for all
`j ∈ J`";
T. Gonzalez and S. Sahni, "Flowshop and jobshop schedules: complexity and approximation",
Operations Research 26 (1978), 36-52, doi:10.1287/opre.26.1.36.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorJobShopTwoTasks

open MetaMathlibExt.Complexity.NPComplete.JobShopScheduling

/-- Well-formedness of an instance of the restriction: the instance is a well-formed JOB-SHOP
SCHEDULING instance, `m = 3`, and every job has at most two tasks. -/
def RestrictedWellFormed (i : JobShopSchedulingInstance) : Prop :=
  WellFormed i ∧ i.1 = 3 ∧ ∀ job ∈ i.2.1, job.length ≤ 2

open Classical in
/-- THREE-PROCESSOR JOB-SHOP SCHEDULING with at most two tasks per job, as a decision
problem over bitstrings. -/
noncomputable def threeProcessorJobShopTwoTasksDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopSchedulingInstance) x with
  | some i => decide (RestrictedWellFormed i ∧ JobShopSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorJobShopTwoTasks
