/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTreeDefs

/-!
# GEOMETRIC CAPACITATED SPANNING TREE with equal requirements: definitions

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

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND6] GEOMETRIC CAPACITATED SPANNING
TREE, comment (reference [Papadimitriou, 1976c]);
C. H. Papadimitriou, "The complexity of the capacitated tree problem", Networks 8 (1978),
217-230, doi:10.1002/net.3230080306.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTreeEqualRequirements



open GeometricCapacitatedSpanningTree (GeometricCapacitatedSpanningTreeInstance)

/-- Well-formedness of an instance: a well-formed GEOMETRIC CAPACITATED SPANNING TREE instance
in which all points other than `p₀` have the same requirement. -/
def WellFormed (i : GeometricCapacitatedSpanningTreeInstance) : Prop :=
  GeometricCapacitatedSpanningTree.WellFormed i ∧
    ∀ u < i.1.length, ∀ v < i.1.length, u ≠ i.2.1 → v ≠ i.2.1 →
      i.2.2.1.getD u 0 = i.2.2.1.getD v 0

open Classical in
/-- GEOMETRIC CAPACITATED SPANNING TREE with equal requirements as a decision problem over
bitstrings. -/
noncomputable def geometricCapacitatedSpanningTreeEqualRequirementsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeometricCapacitatedSpanningTreeInstance) x with
  | some i =>
      decide (WellFormed i ∧
        GeometricCapacitatedSpanningTree.GeometricCapacitatedSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTreeEqualRequirements
