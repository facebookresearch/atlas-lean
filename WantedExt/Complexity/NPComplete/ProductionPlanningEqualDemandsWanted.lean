/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRODUCTION PLANNING with equal demands, equal set-up costs and no inventory costs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 243, problem [SS21] PRODUCTION
PLANNING, comment: "remains NP-complete even if all demands are equal, all set-up costs are
equal, and all inventory costs are 0";
M. Florian, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Deterministic production
planning: algorithms and complexity", Management Science 26 (1980), 669-679,
doi:10.1287/mnsc.26.7.669 (cited by Garey and Johnson as [Lenstra, Rinnooy Kan, and Florian,
1978]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ProductionPlanningWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ProductionPlanningEqualDemands

open MetaMathlibExt.Complexity.NPComplete.ProductionPlanning

/-!
# PRODUCTION PLANNING with equal demands, equal set-up costs and no inventory costs is NP-complete

INSTANCE: a number `n ∈ ℤ⁺` of periods, for each period `i`, `1 ≤ i ≤ n`, a demand `rᵢ = r`,
a production capacity `cᵢ ∈ ℤ₀⁺`, a production set-up cost `bᵢ = b`, an incremental
production cost coefficient `pᵢ ∈ ℤ₀⁺`, and an inventory cost coefficient `hᵢ = 0`, with
common values `r, b ∈ ℤ₀⁺`, and an overall bound `B ∈ ℤ⁺`. QUESTION: do there exist
production amounts `xᵢ ∈ ℤ₀⁺` with inventory levels `Iᵢ = ∑_{j=1}^{i} (xⱼ - rⱼ)` such that all
`xᵢ ≤ cᵢ`, all `Iᵢ ≥ 0`, and `∑_{i=1}^{n} (pᵢ xᵢ + hᵢ Iᵢ) + ∑_{xᵢ > 0} bᵢ ≤ B`?

This is the restriction of PRODUCTION PLANNING
(`WantedExt.Complexity.NPComplete.ProductionPlanningWanted`) to instances in which all
demands are equal, all set-up costs are equal, and all inventory cost coefficients are `0`.
The instance type, its `WellFormed` and `ProductionPlanningFeasible` are reused unchanged; the
restriction is added to well-formedness. All numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance of the restriction: the instance is a well-formed PRODUCTION
PLANNING instance, all periods have the same demand and the same set-up cost, and every
inventory cost coefficient is `0`. -/
def RestrictedWellFormed (i : ProductionPlanningInstance) : Prop :=
  WellFormed i ∧ (∀ p ∈ i.2.1, ∀ q ∈ i.2.1, p.1 = q.1 ∧ p.2.2.1 = q.2.2.1) ∧
    ∀ p ∈ i.2.1, p.2.2.2.2 = 0

open Classical in
/-- PRODUCTION PLANNING with equal demands, equal set-up costs and no inventory costs, as a decision
problem over bitstrings. -/
noncomputable def productionPlanningEqualDemandsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ProductionPlanningInstance) x with
  | some i => decide (RestrictedWellFormed i ∧ ProductionPlanningFeasible i)
  | none => false

/-- **PRODUCTION PLANNING remains NP-complete when all demands are equal, all set-up costs are
equal, and all inventory costs are `0`.** Source: Garey and Johnson (1979), [SS21], comment;
Florian, Lenstra, and Rinnooy Kan (1980). -/
public theorem_wanted productionPlanningEqualDemands_npComplete :
    productionPlanningEqualDemandsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L productionPlanningEqualDemandsDec

end MetaMathlibExt.Complexity.NPComplete.ProductionPlanningEqualDemands
