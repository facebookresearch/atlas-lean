/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED TWO-COMMODITY INTEGRAL FLOW with unit capacities and `R₁ = 1` is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowUnitCapacity

open MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlow

/-!
# DIRECTED TWO-COMMODITY INTEGRAL FLOW with unit capacities and `R₁ = 1` is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s₁`, `s₂`, `t₁`, `t₂`, capacity
`c(a) = 1` for each `a ∈ A`, and requirements `R₁ = 1` and `R₂ ∈ ℤ⁺`. QUESTION: are there two
flow functions `f₁, f₂ : A → ℤ₀⁺` such that `f₁(a) + f₂(a) ≤ c(a)` for each `a ∈ A`, each `fᵢ`
is conserved at every vertex other than `sᵢ` and `tᵢ`, and the net flow of `fᵢ` into `tᵢ` is at
least `Rᵢ`, for `i = 1, 2`?

This is the restriction of DIRECTED TWO-COMMODITY INTEGRAL FLOW
(`WantedExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowWanted`) to instances in
which every arc has capacity `1` and the first requirement is `R₁ = 1`. The instance type, its
`WellFormed` and `DirectedTwoCommodityIntegralFlowFeasible` are reused unchanged; the restriction
is added to well-formedness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **DIRECTED TWO-COMMODITY INTEGRAL FLOW remains NP-complete when every capacity is `1` and
`R₁ = 1`.** Source: Garey and Johnson (1979), [ND38], comment; Even, Itai, and Shamir (1976). -/
public theorem_wanted directedTwoCommodityIntegralFlowUnitCapacity_npComplete :
    unitCapacityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitCapacityDec

end MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowUnitCapacity
