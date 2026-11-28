/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH CONSTRAINED NETWORK FLOW with unit capacities: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND34] PATH CONSTRAINED NETWORK FLOW
(p. 215), comment "Remains NP-complete even if all c(a) = 1" (credited there to H. J. Prömel,
1978).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PathConstrainedNetworkFlowDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathConstrainedNetworkFlowUnit

open MetaMathlibExt.Complexity.NPComplete.PathConstrainedNetworkFlow
  (PathConstrainedNetworkFlowInstance)

/-- Well-formedness of an instance: the parent's (a directed graph on `0, ..., n - 1` with
positive capacities, distinct vertices `s` and `t`, every member of `P` a directed path in `G`,
`0 < R`) and every capacity is `1`. -/
def WellFormed (i : PathConstrainedNetworkFlowInstance) : Prop :=
  PathConstrainedNetworkFlow.WellFormed i ∧ ∀ a ∈ i.2.1, a.2.2 = 1

open Classical in
/-- PATH CONSTRAINED NETWORK FLOW with unit capacities as a decision problem over bitstrings. -/
noncomputable def pathConstrainedNetworkFlowUnitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathConstrainedNetworkFlowInstance) x with
  | some i =>
    decide (WellFormed i ∧ PathConstrainedNetworkFlow.PathConstrainedNetworkFlowFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathConstrainedNetworkFlowUnit
