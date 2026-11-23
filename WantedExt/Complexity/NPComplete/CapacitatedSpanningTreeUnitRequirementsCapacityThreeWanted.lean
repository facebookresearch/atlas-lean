/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITATED SPANNING TREE with unit requirements and capacities 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND5] CAPACITATED SPANNING TREE,
p. 207 (comment: "NP-complete in the strong sense, even if all requirements are 1 and all
capacities are equal to 3");
C. H. Papadimitriou, "The complexity of the capacitated tree problem", Networks 8 (1978),
217-230, doi:10.1002/net.3230080306.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CapacitatedSpanningTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTreeUnitRequirementsCapacityThree

open MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTree
  (CapacitatedSpanningTreeInstance CapacitatedSpanningTreeFeasible)

/-!
# CAPACITATED SPANNING TREE with unit requirements and capacities 3 is NP-complete

INSTANCE: a graph `G = (V, E)`, a specified vertex `v₀ ∈ V`, a capacity `c(e) = 3` and a length
`l(e) ∈ ℤ₀⁺` for each `e ∈ E`, a requirement `r(v) = 1` for each `v ∈ V - {v₀}`, and a bound
`B ∈ ℤ₀⁺`. QUESTION: is there a spanning tree `T` for `G` such that the sum of the lengths of
the edges in `T` does not exceed `B` and such that for each edge `e` in `T`, if `U(e)` is the
set of vertices whose path to `v₀` in `T` contains `e`, then `∑_{u ∈ U(e)} r(u) ≤ c(e)`?

This is the restriction of CAPACITATED SPANNING TREE
(`WantedExt.Complexity.NPComplete.CapacitatedSpanningTreeWanted`, GJ [ND5]) stated in the comment
of [ND5], where it is NP-complete in the strong sense. With all requirements `1` the capacity
condition says that every subtree of `T` hanging below an edge (away from `v₀`) has at most `3`
vertices. The instance type, `CapacitatedSpanningTree.WellFormed` (simple edge list, `v₀` a
vertex, one requirement per vertex) and `CapacitatedSpanningTreeFeasible` are reused unchanged;
the restriction is added to well-formedness: every edge entry has capacity `3`, and every vertex
other than `v₀` has requirement `1`. The requirement entry of `v₀` is not constrained, since the
parent never reads it. Lengths and the bound are arbitrary, in binary. The same comment notes
that with all requirements `1` and all capacities `2` the problem is solvable by weighted
matching.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed CAPACITATED SPANNING TREE instance in which
every edge `(u, v, c, l)` has `c = 3`, and every vertex `v ≠ v₀` has `r(v) = 1`. -/
def WellFormed (i : CapacitatedSpanningTreeInstance) : Prop :=
  CapacitatedSpanningTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2.1 = 3) ∧
    ∀ v < i.1, v ≠ i.2.2.1 → i.2.2.2.1.getD v 0 = 1

open Classical in
/-- CAPACITATED SPANNING TREE with unit requirements and capacities 3 as a decision problem over
bitstrings. -/
noncomputable def capacitatedSpanningTreeUnitRequirementsCapacityThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CapacitatedSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ CapacitatedSpanningTreeFeasible i)
  | none => false

/-- **CAPACITATED SPANNING TREE with all requirements 1 and all capacities 3 is NP-complete.**
Source: Garey and Johnson (1979), [ND5], comment; Papadimitriou (1978). -/
public theorem_wanted capacitatedSpanningTreeUnitRequirementsCapacityThree_npComplete :
    capacitatedSpanningTreeUnitRequirementsCapacityThreeDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L
            capacitatedSpanningTreeUnitRequirementsCapacityThreeDec

end MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTreeUnitRequirementsCapacityThree
