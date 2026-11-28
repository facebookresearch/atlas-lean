/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LEAF SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MAXIMUM LEAF SPANNING
TREE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumLeafSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTree

/-!
# MAXIMUM LEAF SPANNING TREE is NP-complete

An undirected graph and a bound `K`. The question is whether the graph has a spanning tree with
at least `K` leaves. A connected edge set with `n - 1` edges is a tree, so acyclicity need not
be stated separately; the leaf count is witnessed by a list of at least `K` vertices each
incident with exactly one tree edge.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM LEAF SPANNING TREE is NP-complete.** The decision problem MAXIMUM LEAF SPANNING TREE
belongs to NP, and every decision problem in NP reduces to it by a polynomial-time many-one
reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), MAXIMUM LEAF SPANNING TREE. -/
public theorem_wanted maximumLeafSpanningTree_npComplete :
    maximumLeafSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumLeafSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTree
