/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNDIRECTED TWO-COMMODITY INTEGRAL FLOW with unit capacities: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 217, problem [ND39] UNDIRECTED
TWO-COMMODITY INTEGRAL FLOW, comment: "Remains NP-complete even if `c(e) = 1` for all
`e ∈ E`";
S. Even, A. Itai, and A. Shamir, "On the complexity of timetable and
multicommodity flow problems", SIAM Journal on Computing 5 (1976), 691-703,
doi:10.1137/0205048 (the reference Garey and Johnson give for [ND39]).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlowDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlowUnitCapacity

open MetaMathlibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlow

/-- Well-formedness of an instance of the restriction: the instance is a well-formed
UNDIRECTED TWO-COMMODITY INTEGRAL FLOW instance and every edge capacity is `1`. -/
def UnitWellFormed (i : UndirectedTwoCommodityIntegralFlowInstance) : Prop :=
  WellFormed i ∧ ∀ e ∈ i.2.1, e.2.2 = 1

open Classical in
/-- UNDIRECTED TWO-COMMODITY INTEGRAL FLOW with unit capacities, as a decision problem over
bitstrings. -/
noncomputable def unitCapacityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UndirectedTwoCommodityIntegralFlowInstance) x with
  | some i => decide (UnitWellFormed i ∧ UndirectedTwoCommodityIntegralFlowFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlowUnitCapacity
