/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED TWO-COMMODITY INTEGRAL FLOW with s₁ = s₂, t₁ = t₂, restricted arcs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND38] DIRECTED
TWO-COMMODITY INTEGRAL FLOW, p. 216, comment ("Variant in which s₁ = s₂, t₁ = t₂, and arcs
can be restricted to carry only one specified commodity is also NP-complete (follows from
[Even, Itai, and Shamir, 1976])");
S. Even, A. Itai, and A. Shamir, "On the complexity of timetable and
multicommodity flow problems", SIAM Journal on Computing 5 (1976), 691-703,
doi:10.1137/0205048.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowCommonTerminals

/-!
# DIRECTED TWO-COMMODITY INTEGRAL FLOW with s₁ = s₂, t₁ = t₂, restricted arcs is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s₁ = s₂` and `t₁ = t₂`, a capacity
`c(a) ∈ ℤ⁺` for each `a ∈ A`, requirements `R₁, R₂ ∈ ℤ⁺`, and, for some arcs, a restriction to
carry only one specified commodity. QUESTION: are there two flow functions
`f₁, f₂ : A → ℤ₀⁺` such that `f₁(a) + f₂(a) ≤ c(a)` for each `a ∈ A`, each `fᵢ` is conserved
at every vertex other than `sᵢ` and `tᵢ`, the net flow of `fᵢ` into `tᵢ` is at least `Rᵢ`, for
`i = 1, 2`, and every restricted arc carries no flow of the other commodity?

This is the variant of DIRECTED TWO-COMMODITY INTEGRAL FLOW
(`WantedExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowWanted`) recorded in Garey
and Johnson's comment on [ND38]. An instance is an instance of that problem, whose
`WellFormed` (simple directed graph on `0, ..., n - 1`, positive capacities, terminals in
range, positive requirements) is reused, with the two commodities sharing their source and
their sink, together with a list of restrictions `(u, v, k)`: the arc from `u` to `v` may carry
only commodity `k ∈ {1, 2}`. Each arc has at most one restriction. The question is the
question of that problem, with its `capacity` and `CommodityFlow`, plus the restrictions.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open DirectedTwoCommodityIntegralFlow
  (DirectedTwoCommodityIntegralFlowInstance arcs capacity CommodityFlow)

/-- An instance: an instance of DIRECTED TWO-COMMODITY INTEGRAL FLOW (vertex count `n`, arc
records `(u, v, c)`, commodities `(s₁, t₁, R₁)` and `(s₂, t₂, R₂)`) and the arc restrictions
`(u, v, k)`: the arc from `u` to `v` may carry only commodity `k`. -/
abbrev DirectedTwoCommodityIntegralFlowCommonTerminalsInstance :=
  DirectedTwoCommodityIntegralFlowInstance × List (ℕ × ℕ × ℕ)

/-- Well-formedness of an instance: the underlying two-commodity instance is well formed,
`s₁ = s₂` and `t₁ = t₂`, and the restrictions name distinct arcs of the graph, each with a
commodity `k ∈ {1, 2}`. -/
def WellFormed (i : DirectedTwoCommodityIntegralFlowCommonTerminalsInstance) : Prop :=
  DirectedTwoCommodityIntegralFlow.WellFormed i.1 ∧
    i.1.2.2.1.1 = i.1.2.2.2.1 ∧ i.1.2.2.1.2.1 = i.1.2.2.2.2.1 ∧
    (i.2.map fun r => (r.1, r.2.1)).Nodup ∧
    ∀ r ∈ i.2, (r.1, r.2.1) ∈ arcs i.1 ∧ (r.2.2 = 1 ∨ r.2.2 = 2)

/-- There are integral flows `f₁` for commodity 1 and `f₂` for commodity 2 whose sum on each arc
is at most its capacity, such that an arc restricted to commodity 1 carries no flow `f₂` and an
arc restricted to commodity 2 carries no flow `f₁`. -/
def DirectedTwoCommodityIntegralFlowCommonTerminalsFeasible
    (i : DirectedTwoCommodityIntegralFlowCommonTerminalsInstance) : Prop :=
  ∃ f₁ f₂ : Fin i.1.1 → Fin i.1.1 → ℕ,
    (∀ u v, f₁ u v + f₂ u v ≤ capacity i.1 u v) ∧
      CommodityFlow i.1 i.1.2.2.1 f₁ ∧ CommodityFlow i.1 i.1.2.2.2 f₂ ∧
      ∀ r ∈ i.2, ∀ u v : Fin i.1.1, (u : ℕ) = r.1 → (v : ℕ) = r.2.1 →
        (r.2.2 = 1 → f₂ u v = 0) ∧ (r.2.2 = 2 → f₁ u v = 0)

open Classical in
/-- DIRECTED TWO-COMMODITY INTEGRAL FLOW with common terminals and commodity-restricted arcs,
as a decision problem over bitstrings. -/
noncomputable def directedTwoCommodityIntegralFlowCommonTerminalsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedTwoCommodityIntegralFlowCommonTerminalsInstance) x with
  | some i => decide (WellFormed i ∧ DirectedTwoCommodityIntegralFlowCommonTerminalsFeasible i)
  | none => false

/-- **DIRECTED TWO-COMMODITY INTEGRAL FLOW with `s₁ = s₂`, `t₁ = t₂` and commodity-restricted
arcs is NP-complete.** Source: Garey and Johnson (1979), [ND38], comment; Even, Itai, and
Shamir (1976). -/
public theorem_wanted directedTwoCommodityIntegralFlowCommonTerminals_npComplete :
    directedTwoCommodityIntegralFlowCommonTerminalsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedTwoCommodityIntegralFlowCommonTerminalsDec

end MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlowCommonTerminals
