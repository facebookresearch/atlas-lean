/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on bipartite planar graphs of maximum degree 4 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET (the parent
problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_1153` (bipartite ∩
maximum degree 4 ∩ planar), problem Feedback vertex set: NP-complete (reference note 1593, V. B.
Le: "Feedback vertex set is NP-complete for planar graph of maximum degree 4. By subdividing each
edge by one new vertex, it easily follows that feedback vertex set is also NP-complete on
bipartite planar graphs of maximum degree 4").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetBipartitePlanarMaxDegreeFourDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetBipartitePlanarMaxDegreeFour

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)

/-!
# FEEDBACK VERTEX SET on bipartite planar graphs of maximum degree 4 is NP-complete

INSTANCE: a bipartite planar graph `G = (V, E)` in which every vertex has degree at most `4`,
and a positive integer `K ≤ |V|`.
QUESTION: is there a set `S ⊆ V` of at most `K` vertices such that every cycle of `G` contains a
vertex of `S`, i.e. `G - S` is a forest?

This is FEEDBACK VERTEX SET ([GT7]) on the ISGCI class `gc_1153`. ISGCI lists it as NP-complete
with reference note 1593 (V. B. Le): the problem is NP-complete on planar graphs of maximum degree
`4` (`FeedbackVertexSetPlanarMaxDegreeFourWanted`), and subdividing every edge by one new vertex
keeps the graph planar with maximum degree `4` and makes it bipartite. The subdivision does not
change the minimum size of a feedback vertex set: the cycles correspond, and a subdivision vertex
in a feedback vertex set can be replaced by an endpoint of its edge. Adding a disjoint 4-cycle
raises the minimum by exactly one and keeps the graph bipartite and planar with maximum degree
`4`. A bound `K ≥ |V|` already gives a yes-instance (take `S = V`), so mapping `(G, K)` to the
subdivided graph plus a disjoint 4-cycle with bound `min K |V| + 1` (positive, also for `K = 0`,
and at most `|V| + 1`, which is below the new vertex count) reduces the planar maximum-degree-`4`
problem to the restriction.
Bipartiteness, planarity and degrees are checked in polynomial time, and a feedback vertex set is a
certificate, so the problem is in NP.

The instance, its graph, the planar maximum-degree-`4` well-formedness (a simple edge list,
MathlibExt's `SimpleGraph.IsPlanar`, every Mathlib `SimpleGraph.degree` at most `4`) and the
question (`G - S` acyclic for some `|S| ≤ K`) are those of
`FeedbackVertexSetPlanarMaxDegreeFourWanted` and `FeedbackVertexSetWanted`; this module adds
bipartiteness (Mathlib's `SimpleGraph.IsBipartite`) and Garey and Johnson's bound `0 < K ≤ |V|`
([GT7], as in `FeedbackVertexSetPlanarWanted`) to well-formedness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FEEDBACK VERTEX SET on bipartite planar graphs of maximum degree 4 is NP-complete.**
Source: Garey and Johnson (1979), [GT7]; ISGCI class `gc_1153` (reference note 1593). -/
public theorem_wanted feedbackVertexSetBipartitePlanarMaxDegreeFour_npComplete :
    feedbackVertexSetBipartitePlanarMaxDegreeFourDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetBipartitePlanarMaxDegreeFourDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetBipartitePlanarMaxDegreeFour
