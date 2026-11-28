/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ISOMORPHIC SPANNING TREE for full binary trees is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND8] ISOMORPHIC SPANNING TREE
(p. 207), comment "Remains NP-complete even if ... (b) T is a full binary tree [Papadimitriou
and Yannakakis, 1978]";
C. H. Papadimitriou and M. Yannakakis, "The complexity of restricted spanning tree problems",
Journal of the ACM 29(2) (1982), 285-309, doi:10.1145/322307.322309.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IsomorphicSpanningTreeFullBinaryDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTreeFullBinary

open MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTree

/-!
# ISOMORPHIC SPANNING TREE for full binary trees is NP-complete

INSTANCE: a graph `G = (V, E)` and a full binary tree `T = (V_T, E_T)`. QUESTION: does `G`
contain a spanning tree isomorphic to `T`?

This is the restriction of ISOMORPHIC SPANNING TREE ([ND8], `IsomorphicSpanningTreeWanted`) to
full binary trees `T`. The instance type, `IsomorphicSpanningTree.WellFormed` (simple edge
lists, `T` a tree) and `IsomorphicSpanningTree.IsomorphicSpanningTreeFeasible` are the parent's,
unchanged; `WellFormed` adds that `T` is a full binary tree.

A full binary tree is a rooted tree in which every vertex has either no children or exactly two
children. `T` is given unrooted, so `IsFullBinary` asks that `T` be a tree with a vertex `r` to
serve as the root: `T` has one vertex, or `r` has degree `2` (its two children) and every other
vertex has degree `1` (a leaf: its parent only) or `3` (its parent and two children). Rooting
the tree at `r` shows that this is exactly the rooted definition. Garey and Johnson do not
define the term; the complete binary trees (all leaves at one depth) are among these trees, so a
narrower reading of the source is a special case of this statement.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ISOMORPHIC SPANNING TREE is NP-complete for full binary trees.** Source: Garey and
Johnson (1979), [ND8], comment (b); Papadimitriou and Yannakakis (1978; published 1982). -/
public theorem_wanted isomorphicSpanningTreeFullBinary_npComplete :
    isomorphicSpanningTreeFullBinaryDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L isomorphicSpanningTreeFullBinaryDec

end MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTreeFullBinary
