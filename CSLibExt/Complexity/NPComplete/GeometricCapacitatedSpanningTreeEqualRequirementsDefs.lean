/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC CAPACITATED SPANNING TREE with equal requirements: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND6] GEOMETRIC CAPACITATED SPANNING
TREE, comment (reference [Papadimitriou, 1976c]);
C. H. Papadimitriou, "The complexity of the capacitated tree problem", Networks 8 (1978),
217-230, doi:10.1002/net.3230080306.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricCapacitatedSpanningTreeDefs

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
