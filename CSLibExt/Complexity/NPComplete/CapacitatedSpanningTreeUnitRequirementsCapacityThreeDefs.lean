/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITATED SPANNING TREE with unit requirements and capacities 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND5] CAPACITATED SPANNING TREE,
p. 207 (comment: "NP-complete in the strong sense, even if all requirements are 1 and all
capacities are equal to 3");
C. H. Papadimitriou, "The complexity of the capacitated tree problem", Networks 8 (1978),
217-230, doi:10.1002/net.3230080306.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CapacitatedSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTreeUnitRequirementsCapacityThree

open MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTree
  (CapacitatedSpanningTreeInstance CapacitatedSpanningTreeFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTreeUnitRequirementsCapacityThree
