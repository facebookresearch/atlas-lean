/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JOB-SHOP SCHEDULING with two processors and at most three tasks per job: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP SCHEDULING, p. 242
(comment: "NP-complete (in the ordinary sense) if `m = 2` and `n_j ≤ 3` for all `j ∈ J`");
T. Gonzalez and S. Sahni, "Flowshop and jobshop schedules: complexity and approximation",
Operations Research 26 (1978), 36-52, doi:10.1287/opre.26.1.36.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorJobShopThreeTasks

/-- Well-formedness of an instance: the parent's (`0 < m`, `1 ≤ n_j`, processors in
`{1, …, m}`, consecutive tasks of a job on different processors, `0 < D`), `m = 2`, and every
job has at most three tasks. -/
def WellFormed (i : JobShopScheduling.JobShopSchedulingInstance) : Prop :=
  JobShopScheduling.WellFormed i ∧ i.1 = 2 ∧ ∀ job ∈ i.2.1, job.length ≤ 3

open Classical in
/-- JOB-SHOP SCHEDULING with two processors and at most three tasks per job, as a decision
problem over bitstrings. -/
noncomputable def twoProcessorJobShopThreeTasksDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopScheduling.JobShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ JobShopScheduling.JobShopSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorJobShopThreeTasks
