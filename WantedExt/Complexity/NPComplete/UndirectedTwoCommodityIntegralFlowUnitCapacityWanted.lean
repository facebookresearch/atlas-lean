/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNDIRECTED TWO-COMMODITY INTEGRAL FLOW with unit capacities is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlowWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlowUnitCapacity

open MetaMathlibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlow

/-!
# UNDIRECTED TWO-COMMODITY INTEGRAL FLOW with unit capacities is NP-complete

INSTANCE: a graph `G = (V, E)`, specified vertices `s₁`, `s₂`, `t₁`, `t₂`, capacity `c(e) = 1`
for each `e ∈ E`, and requirements `R₁, R₂ ∈ ℤ⁺`. QUESTION: are there two flow functions
`f₁, f₂ : {(u, v), (v, u) : {u, v} ∈ E} → ℤ₀⁺` meeting the joint capacity condition on each
edge, each conserved at every vertex other than its own source and sink, with the net flow of
`fᵢ` into `tᵢ` at least `Rᵢ`, for `i = 1, 2`?

This is the restriction of UNDIRECTED TWO-COMMODITY INTEGRAL FLOW
(`WantedExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlowWanted`) to instances in
which every edge has capacity `1`. The instance type, its `WellFormed` and
`UndirectedTwoCommodityIntegralFlowFeasible` (including its form of the joint capacity
condition) are reused unchanged; the restriction is added to well-formedness. With unit
capacities the capacity condition says that each edge carries one unit of one commodity in one
direction, or nothing: the flows are edge-disjoint.

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

/-- **UNDIRECTED TWO-COMMODITY INTEGRAL FLOW remains NP-complete when every capacity is `1`.**
Source: Garey and Johnson (1979), [ND39], comment; Even, Itai, and Shamir (1976). -/
public theorem_wanted undirectedTwoCommodityIntegralFlowUnitCapacity_npComplete :
    unitCapacityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitCapacityDec

end MetaMathlibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlowUnitCapacity
