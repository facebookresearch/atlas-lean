/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR OPEN-SHOP SCHEDULING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING, comment:
remains NP-complete if `m = 3`;
T. Gonzalez and S. Sahni, "Open shop scheduling to minimize finish time", Journal of the ACM 23
(1976), 665-679, doi:10.1145/321978.321985.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.OpenShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOpenShopScheduling

/-- Well-formedness of an instance: it is a well-formed OPEN-SHOP SCHEDULING instance (`0 < m`,
every job has `m` tasks, `0 < D`) with `m = 3` processors. -/
def WellFormed (i : OpenShopScheduling.OpenShopSchedulingInstance) : Prop :=
  NoWaitFlowShopScheduling.WellFormed i ∧ i.1 = 3

open Classical in
/-- THREE-PROCESSOR OPEN-SHOP SCHEDULING as a decision problem over bitstrings. -/
noncomputable def threeProcessorOpenShopSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenShopScheduling.OpenShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ OpenShopScheduling.OpenShopSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorOpenShopScheduling
