/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED DIAMETER SPANNING TREE with a fixed bound `D ≥ 4` and weights 1 or 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND4] BOUNDED DIAMETER
SPANNING TREE, p. 206, comment ("Remains NP-complete for any fixed D ≥ 4, even if all edge
weights are either 1 or 2"; reference: [Garey and Johnson, unpublished], transformation from
EXACT COVER BY 3-SETS).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BoundedDiameterSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedDiameterSpanningTreeFixedD

open BoundedDiameterSpanningTree
  (BoundedDiameterSpanningTreeInstance BoundedDiameterSpanningTreeFeasible)

/-- Well-formedness of an instance for the fixed diameter bound `D`: the parent's (a simple
weighted edge list on `Fin n` with positive weights, `0 < D ≤ |V|`, `0 < B`), the instance's
diameter bound is `D`, and every edge weight is `1` or `2`. -/
def WellFormed (D : ℕ) (i : BoundedDiameterSpanningTreeInstance) : Prop :=
  BoundedDiameterSpanningTree.WellFormed i ∧ i.2.2.1 = D ∧
    ∀ e ∈ i.2.1, e.2.2 = 1 ∨ e.2.2 = 2

open Classical in
/-- BOUNDED DIAMETER SPANNING TREE with the diameter bound fixed to `D` and edge weights 1 or 2,
as a decision problem over bitstrings. -/
noncomputable def boundedDiameterSpanningTreeFixedDDec (D : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedDiameterSpanningTreeInstance) x with
  | some i => decide (WellFormed D i ∧ BoundedDiameterSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BoundedDiameterSpanningTreeFixedD
