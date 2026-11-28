/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC CAPACITATED SPANNING TREE with equal requirements is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND6] GEOMETRIC CAPACITATED SPANNING
TREE, comment (reference [Papadimitriou, 1976c]);
C. H. Papadimitriou, "The complexity of the capacitated tree problem", Networks 8 (1978),
217-230, doi:10.1002/net.3230080306.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTreeEqualRequirementsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTreeEqualRequirements

/-!
# GEOMETRIC CAPACITATED SPANNING TREE with equal requirements is NP-complete

INSTANCE: a set `P ⊆ Z × Z` of points in the plane, a specified point `p₀ ∈ P`, a requirement
`r(p) ∈ Z₀⁺` for each `p ∈ P - p₀`, all equal, a capacity `c ∈ Z⁺`, and a bound `B ∈ Z⁺`.
QUESTION: is there a spanning tree `T = (P, E')` for the complete graph on `P` with
`∑_{e ∈ E'} d(e) ≤ B` (`d` the discretized Euclidean distance) such that for each `e ∈ E'` the
requirements of the vertices whose paths to `p₀` pass through `e` sum to at most `c`?

This is GEOMETRIC CAPACITATED SPANNING TREE
(`WantedExt.Complexity.NPComplete.GeometricCapacitatedSpanningTreeWanted`, Garey and Johnson
[ND6], reference [Papadimitriou, 1976c]) restricted as in the [ND6] comment: "Remains
NP-complete even if all requirements are equal." The instance type,
`GeometricCapacitatedSpanningTree.WellFormed` and
`GeometricCapacitatedSpanningTree.GeometricCapacitatedSpanningTreeFeasible` are reused
unchanged; the restriction adds to well-formedness that the requirements of any two points
other than `p₀` are equal (the entry of `p₀` is never read).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open GeometricCapacitatedSpanningTree (GeometricCapacitatedSpanningTreeInstance)

/-- **GEOMETRIC CAPACITATED SPANNING TREE is NP-complete with equal requirements.** Source:
Garey and Johnson (1979), [ND6], comment; Papadimitriou (1978). -/
public theorem_wanted geometricCapacitatedSpanningTreeEqualRequirements_npComplete :
    geometricCapacitatedSpanningTreeEqualRequirementsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L geometricCapacitatedSpanningTreeEqualRequirementsDec

end MetaMathlibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTreeEqualRequirements
