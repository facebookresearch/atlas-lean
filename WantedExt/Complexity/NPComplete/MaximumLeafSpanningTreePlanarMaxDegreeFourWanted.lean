/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LEAF SPANNING TREE on planar graphs of maximum degree 4 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND2] MAXIMUM LEAF SPANNING TREE,
comment on p. 206 ("Remains NP-complete ... if G is planar with no degree exceeding 4";
reference [Garey and Johnson, ——], unpublished results);
A. Reich, "Complexity of the maximum leaf spanning tree problem on planar and regular graphs",
Theoretical Computer Science 626 (2016), 134-143, doi:10.1016/j.tcs.2016.02.011, Section 1
(records the planar maximum-degree-4 case with its attribution to Garey and Johnson).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumLeafSpanningTreePlanarMaxDegreeFourDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTreePlanarMaxDegreeFour

open MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTree
  (MaximumLeafSpanningTreeInstance MaximumLeafSpanningTreeFeasible)

/-!
# MAXIMUM LEAF SPANNING TREE on planar graphs of maximum degree 4 is NP-complete

INSTANCE: a planar graph `G = (V, E)` with no vertex degree exceeding 4, and a positive integer
`K ≤ |V|`.
QUESTION: is there a spanning tree for `G` in which `K` or more vertices have degree 1?

The instance and the question are those of MAXIMUM LEAF SPANNING TREE
(`WantedExt.Complexity.NPComplete.MaximumLeafSpanningTreeWanted`: a nonempty simple graph on
`Fin n` given by an edge list, and the bound `K`; the question asks for `n - 1` distinct edges of
`G` forming a connected spanning subgraph, hence a spanning tree, together with at least `K`
vertices each incident with exactly one of its edges). The restriction adds that the graph is
planar, the repository's `SimpleGraph.IsPlanar` (`MathlibExt`: a crossing-free straight-line
drawing, which by Fáry's theorem exists exactly for planar graphs), that every vertex has
degree at most 4 (Mathlib's `SimpleGraph.degree`), and, as in the source, `0 < K ≤ |V|`.

Garey and Johnson state this case in the entry whose reference is their own unpublished results
(a transformation from DOMINATING SET); Reich (2016) records it with that attribution. Membership
in NP is inherited: the certificate is the tree and its leaves, and planarity (Hopcroft and
Tarjan) and the degree bound are checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM LEAF SPANNING TREE on planar graphs of maximum degree 4 is NP-complete.** Source:
Garey and Johnson (1979), [ND2]; Reich (2016). -/
public theorem_wanted maximumLeafSpanningTreePlanarMaxDegreeFour_npComplete :
    maximumLeafSpanningTreePlanarMaxDegreeFourDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumLeafSpanningTreePlanarMaxDegreeFourDec

end MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTreePlanarMaxDegreeFour
