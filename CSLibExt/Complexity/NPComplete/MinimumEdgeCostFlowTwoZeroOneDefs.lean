/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM EDGE-COST FLOW with capacities 2 and prices 0/1: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND32] MINIMUM EDGE-COST FLOW (p. 214),
comment "Remains NP-complete if c(a) = 2 and p(a) ∈ {0,1} for all a ∈ A" (credited there to
S. Even and D. S. Johnson, 1977, unpublished).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumEdgeCostFlowDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumEdgeCostFlowTwoZeroOne

open MetaMathlibExt.Complexity.NPComplete.MinimumEdgeCostFlow (MinimumEdgeCostFlowInstance)

/-- Well-formedness of an instance: the parent's (a directed graph on `0, ..., n - 1`, positive
capacities, distinct vertices `s` and `t`, `0 < R`, `0 < B`), every capacity is `2`, and every
price is `0` or `1`. -/
def WellFormed (i : MinimumEdgeCostFlowInstance) : Prop :=
  MinimumEdgeCostFlow.WellFormed i ∧ ∀ a ∈ i.2.1, a.2.2.1 = 2 ∧ (a.2.2.2 = 0 ∨ a.2.2.2 = 1)

open Classical in
/-- MINIMUM EDGE-COST FLOW with capacities `2` and prices `0`/`1` as a decision problem over
bitstrings. -/
noncomputable def minimumEdgeCostFlowTwoZeroOneDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumEdgeCostFlowInstance) x with
  | some i => decide (WellFormed i ∧ MinimumEdgeCostFlow.MinimumEdgeCostFlowFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumEdgeCostFlowTwoZeroOne
