/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRODUCTION PLANNING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS21] PRODUCTION
PLANNING;
M. Florian, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Deterministic production
planning: algorithms and complexity", Management Science 26 (1980), 669-679,
doi:10.1287/mnsc.26.7.669.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ProductionPlanningDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ProductionPlanning

/-!
# PRODUCTION PLANNING is NP-complete

INSTANCE: a number `n ∈ ℤ⁺` of periods, for each period `i`, `1 ≤ i ≤ n`, a demand
`rᵢ ∈ ℤ₀⁺`, a production capacity `cᵢ ∈ ℤ₀⁺`, a production set-up cost `bᵢ ∈ ℤ₀⁺`, an
incremental production cost coefficient `pᵢ ∈ ℤ₀⁺`, and an inventory cost coefficient
`hᵢ ∈ ℤ₀⁺`, and an overall bound `B ∈ ℤ⁺`.
QUESTION: do there exist production amounts `xᵢ ∈ ℤ₀⁺` and associated inventory levels
`Iᵢ = ∑_{j=1}^{i} (xⱼ - rⱼ)`, `1 ≤ i ≤ n`, such that all `xᵢ ≤ cᵢ`, all `Iᵢ ≥ 0`, and
`∑_{i=1}^{n} (pᵢ xᵢ + hᵢ Iᵢ) + ∑_{xᵢ > 0} bᵢ ≤ B`?

Inventory levels and costs are computed in `ℤ`. Periods are numbered from `0` below. All
numbers use the canonical binary encoding; the problem is NP-complete in the ordinary sense
(it is solvable in pseudo-polynomial time).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PRODUCTION PLANNING is NP-complete.** Source: Garey and Johnson (1979), [SS21]; Florian,
Lenstra, and Rinnooy Kan (1980). -/
public theorem_wanted productionPlanning_npComplete :
    productionPlanningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L productionPlanningDec

end MetaMathlibExt.Complexity.NPComplete.ProductionPlanning
