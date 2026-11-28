/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED DIAMETER SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND4] BOUNDED DIAMETER
SPANNING TREE, p. 206 (reference: [Garey and Johnson, unpublished], transformation from
EXACT COVER BY 3-SETS).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BoundedDiameterSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedDiameterSpanningTree

/-!
# BOUNDED DIAMETER SPANNING TREE is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight `w(e) ∈ ℤ⁺` for each `e ∈ E`, a positive integer
`D ≤ |V|`, and a positive integer `B`. QUESTION: is there a spanning tree `T` for `G` such that
the sum of the weights of the edges in `T` does not exceed `B` and such that `T` contains no
simple path with more than `D` edges?

The vertices are `Fin n` and the graph is given by a simple edge list with weights (an entry
`(u, v, w)` is the edge `{u, v}` of weight `w`). A spanning tree of `G` is a Mathlib
`SimpleGraph` `T` on the vertices of `G` with `T ≤ G` and `T.IsTree`, the form of Mathlib's
`SimpleGraph.Connected.exists_isTree_le`. A simple path in `T` is a `SimpleGraph.Walk` with
`SimpleGraph.Walk.IsPath`, and its number of edges is `SimpleGraph.Walk.length`. Weights are in
binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BOUNDED DIAMETER SPANNING TREE is NP-complete.** Source: Garey and Johnson (1979), [ND4]
(attributed there to Garey and Johnson, unpublished). -/
public theorem_wanted boundedDiameterSpanningTree_npComplete :
    boundedDiameterSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boundedDiameterSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.BoundedDiameterSpanningTree
