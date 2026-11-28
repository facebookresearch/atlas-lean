/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN-SHOP SCHEDULING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING;
T. Gonzalez and S. Sahni, "Open shop scheduling to minimize finish time", Journal of the ACM 23
(1976), 665-679, doi:10.1145/321978.321985.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.NoWaitFlowShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OpenShopScheduling

/-- An instance: the number of processors `m`, one list of task lengths
`(l(t_1[j]), …, l(t_m[j]))` per job `j`, and the deadline `D` (the instance type of
`NoWaitFlowShopSchedulingWanted`). -/
abbrev OpenShopSchedulingInstance := NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance

/-- Some open-shop schedule `σ p j` (start of job `j`'s task on processor `p`) meets the
deadline: `NoWaitFlowShopScheduling.IsOpenShopSchedule`, i.e., every `σ p` is one-to-one,
`σ p k < σ p j` implies `σ p k + l(t_p[k]) ≤ σ p j`, the tasks of each job occupy pairwise
disjoint intervals, and every task ends by `D`. -/
def OpenShopSchedulingFeasible (i : OpenShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, NoWaitFlowShopScheduling.IsOpenShopSchedule i σ

open Classical in
/-- OPEN-SHOP SCHEDULING as a decision problem over bitstrings. -/
noncomputable def openShopSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenShopSchedulingInstance) x with
  | some i => decide (NoWaitFlowShopScheduling.WellFormed i ∧ OpenShopSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OpenShopScheduling
