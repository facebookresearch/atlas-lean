/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BoundedDiameterSpanningTreeDefs

/-!
# BOUNDED DIAMETER SPANNING TREE with a fixed bound `D ≥ 4` and weights 1 or 2: definitions

For a fixed constant `D ≥ 4`: INSTANCE: a graph `G = (V, E)`, a weight `w(e) ∈ {1, 2}` for each
`e ∈ E`, and a positive integer `B`. QUESTION: is there a spanning tree `T` for `G` such that the
sum of the weights of the edges in `T` does not exceed `B` and such that `T` contains no simple
path with more than `D` edges?

Garey and Johnson record in the comment to [ND4] that the problem "remains NP-complete for any
fixed `D ≥ 4`, even if all edge weights are either 1 or 2", crediting their own unpublished
work (the original was not available); the entry adds that it "can be solved easily in
polynomial time if `D ≤ 3`, or if all edge weights are equal".

This is the restriction of BOUNDED DIAMETER SPANNING TREE ([ND4],
`BoundedDiameterSpanningTreeWanted`) to instances whose diameter bound is `D`, for a constant
`D` that is not part of the input, and whose edge weights are 1 or 2. The instance type,
`BoundedDiameterSpanningTree.WellFormed` and
`BoundedDiameterSpanningTree.BoundedDiameterSpanningTreeFeasible` are the parent's, unchanged;
`WellFormed D` adds that the instance's diameter bound is `D` and that every edge weight is `1`
or `2`. The parent's condition `D ≤ |V|` is kept, so for fixed `D` only graphs with at least
`D` vertices are instances (on fewer vertices no tree has a path with `D` edges), as in
`DegreeBoundedConnectedSubgraphFixedDWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND4] BOUNDED DIAMETER
SPANNING TREE, p. 206, comment ("Remains NP-complete for any fixed D ≥ 4, even if all edge
weights are either 1 or 2"; reference: [Garey and Johnson, unpublished], transformation from
EXACT COVER BY 3-SETS).
-/

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
