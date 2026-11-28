/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITATED SPANNING TREE with capacities 2 and 0-1 requirements and lengths: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND5] CAPACITATED SPANNING TREE,
comment (p. 207): "remains NP-complete if all capacities are 2, all requirements 0 or 1, and all
edge lengths 0 or 1 [Even and Johnson, 1977]" (S. Even and D. S. Johnson, unpublished results,
1977, as listed in Garey and Johnson's references).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CapacitatedSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTreeCapacityTwo

open CapacitatedSpanningTree (CapacitatedSpanningTreeInstance CapacitatedSpanningTreeFeasible)

/-- Well-formedness of an instance: a well-formed CAPACITATED SPANNING TREE instance in which
every edge `(u, v, c, l)` has `c = 2` and `l ≤ 1`, and every vertex `v ≠ v₀` has `r(v) ≤ 1`. -/
def WellFormed (i : CapacitatedSpanningTreeInstance) : Prop :=
  CapacitatedSpanningTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2.1 = 2 ∧ e.2.2.2 ≤ 1) ∧
    ∀ v < i.1, v ≠ i.2.2.1 → i.2.2.2.1.getD v 0 ≤ 1

open Classical in
/-- CAPACITATED SPANNING TREE with capacities 2 and 0-1 requirements and lengths as a decision
problem over bitstrings. -/
noncomputable def capacitatedSpanningTreeCapacityTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CapacitatedSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ CapacitatedSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CapacitatedSpanningTreeCapacityTwo
