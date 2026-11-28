/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED DIAMETER SPANNING TREE with a fixed bound `D ≥ 4` and weights 1 or 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND4] BOUNDED DIAMETER
SPANNING TREE, p. 206, comment ("Remains NP-complete for any fixed D ≥ 4, even if all edge
weights are either 1 or 2"; reference: [Garey and Johnson, unpublished], transformation from
EXACT COVER BY 3-SETS).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BoundedDiameterSpanningTreeFixedDDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedDiameterSpanningTreeFixedD

open BoundedDiameterSpanningTree
  (BoundedDiameterSpanningTreeInstance BoundedDiameterSpanningTreeFeasible)

/-!
# BOUNDED DIAMETER SPANNING TREE with a fixed bound `D ≥ 4` and weights 1 or 2 is NP-complete

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

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BOUNDED DIAMETER SPANNING TREE is NP-complete for every fixed `D ≥ 4`, even with edge
weights 1 or 2.** Source: Garey and Johnson (1979), [ND4], comment (Garey and Johnson,
unpublished). -/
public theorem_wanted boundedDiameterSpanningTreeFixedD_npComplete (D : ℕ) (hD : 4 ≤ D) :
    boundedDiameterSpanningTreeFixedDDec D ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (boundedDiameterSpanningTreeFixedDDec D)

end MetaMathlibExt.Complexity.NPComplete.BoundedDiameterSpanningTreeFixedD
