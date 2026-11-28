/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED TWO-COMMODITY INTEGRAL FLOW with unit capacities and `R₁ = 1`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 216, problem [ND38] DIRECTED
TWO-COMMODITY INTEGRAL FLOW, comment: "Remains NP-complete even if `c(a) = 1` for all
`a ∈ A` and `R₁ = 1`";
S. Even, A. Itai, and A. Shamir, "On the complexity of timetable and
multicommodity flow problems", SIAM Journal on Computing 5 (1976), 691-703,
doi:10.1137/0205048 (the reference Garey and Johnson give for [ND38]).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowUnitCapacity

open MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlow

/-- Well-formedness of an instance of the restriction: the instance is a well-formed
DIRECTED TWO-COMMODITY INTEGRAL FLOW instance, every arc capacity is `1`, and `R₁ = 1`. -/
def UnitWellFormed (i : DirectedTwoCommodityIntegralFlowInstance) : Prop :=
  WellFormed i ∧ (∀ a ∈ i.2.1, a.2.2 = 1) ∧ i.2.2.1.2.2 = 1

open Classical in
/-- DIRECTED TWO-COMMODITY INTEGRAL FLOW with unit capacities and `R₁ = 1`, as a decision
problem over bitstrings. -/
noncomputable def unitCapacityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedTwoCommodityIntegralFlowInstance) x with
  | some i => decide (UnitWellFormed i ∧ DirectedTwoCommodityIntegralFlowFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowUnitCapacity
