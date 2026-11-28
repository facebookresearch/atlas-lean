/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITATED SPANNING TREE with capacities 2 and 0-1 requirements and lengths is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND5] CAPACITATED SPANNING TREE,
comment (p. 207): "remains NP-complete if all capacities are 2, all requirements 0 or 1, and all
edge lengths 0 or 1 [Even and Johnson, 1977]" (S. Even and D. S. Johnson, unpublished results,
1977, as listed in Garey and Johnson's references).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CapacitatedSpanningTreeCapacityTwoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTreeCapacityTwo

open CapacitatedSpanningTree (CapacitatedSpanningTreeInstance CapacitatedSpanningTreeFeasible)

/-!
# CAPACITATED SPANNING TREE with capacities 2 and 0-1 requirements and lengths is NP-complete

INSTANCE: a graph `G = (V, E)`, a specified vertex `v₀ ∈ V`, a capacity `c(e) = 2` and a length
`l(e) ∈ {0, 1}` for each `e ∈ E`, a requirement `r(v) ∈ {0, 1}` for each `v ∈ V - {v₀}`, and a
bound `B ∈ ℤ₀⁺`. QUESTION: is there a spanning tree `T` for `G` such that the sum of the lengths
of the edges in `T` does not exceed `B` and such that for each edge `e` in `T`, if `U(e)` is the
set of vertices whose path to `v₀` in `T` contains `e`, then `∑_{u ∈ U(e)} r(u) ≤ c(e)`?

This is the restriction of CAPACITATED SPANNING TREE
(`WantedExt.Complexity.NPComplete.CapacitatedSpanningTreeWanted`, GJ [ND5]) stated in the comment
of [ND5]. The instance type, `CapacitatedSpanningTree.WellFormed` (simple edge list, `v₀` a
vertex, one requirement per vertex) and `CapacitatedSpanningTreeFeasible` are reused unchanged;
the restriction is added to well-formedness: every edge entry has capacity `2` and length at most
`1`, and every vertex other than `v₀` has requirement at most `1`. The requirement entry of `v₀`
is not constrained, since the parent never reads it. The same comment notes that with all
capacities `1` (and 0-1 requirements) the problem is solvable by minimum-cost flow, and that with
all requirements `1` and all capacities `2` it is solvable by weighted matching.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CAPACITATED SPANNING TREE with capacities 2 and 0-1 requirements and lengths is
NP-complete.** Source: Garey and Johnson (1979), [ND5], comment (Even and Johnson, 1977). -/
public theorem_wanted capacitatedSpanningTreeCapacityTwo_npComplete :
    capacitatedSpanningTreeCapacityTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L capacitatedSpanningTreeCapacityTwoDec

end MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTreeCapacityTwo
