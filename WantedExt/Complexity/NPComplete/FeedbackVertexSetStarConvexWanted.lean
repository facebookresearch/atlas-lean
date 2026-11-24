/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on star convex bipartite graphs is NP-complete

Source:
W. Jiang, T. Liu, T. Ren and K. Xu, "Two hardness results on feedback vertex sets", Frontiers in
Algorithmics and Algorithmic Aspects in Information and Management (FAW-AAIM 2011), Lecture Notes
in Computer Science 6681 (2011), 233-243, doi:10.1007/978-3-642-21204-8_26;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET (undirected version in
the comment);
ISGCI (https://www.graphclasses.org/classes/gc_1151.html), problem "Feedback vertex set" on star
convex graphs: NP-complete, with the attribution to Jiang, Liu, Ren and Xu.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Star
public import WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetStarConvex

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)

/-!
# FEEDBACK VERTEX SET on star convex bipartite graphs is NP-complete

INSTANCE: a star convex bipartite graph `G = (V, E)` and a positive integer `K`.
QUESTION: is there a set `S ⊆ V` of at most `K` vertices such that `G - S` is a forest?

A bipartite graph `B = (X, Y, E)` is star convex (ISGCI class `gc_1151`; Jiang, Liu, Ren and Xu,
Section 1) if there is a tree `T` on `X` that is a star such that, for every `y ∈ Y`, the
neighbourhood of `y` induces a subtree of `T`. Here the sides are a set `X` of vertices and its
complement, every edge joins `X` to its complement, the star on `X` with centre `c` is Mathlib's
`SimpleGraph.starGraph c` (a tree, `isTree_starGraph`), and "induces a subtree" says that the
subgraph of the star induced on `N(y)` is preconnected (Mathlib's `Preconnected`; for a nonempty
set this is `Connected`, and a connected induced subgraph of a tree is a subtree). An isolated `y`
has an empty neighbourhood, which this allows. The star needs a centre in `X`, so `X` is nonempty
and the graph with no vertices is not star convex.

The instance, its graph, its well-formedness (a simple edge list; this module adds `0 < K`, as
the cited problem has a positive integer bound) and the question (`G - S`
acyclic for some `|S| ≤ K`) are those of FEEDBACK VERTEX SET (`FeedbackVertexSetWanted`); this
module adds the class restriction to well-formedness, as `FeedbackVertexSetBipartiteWanted` does
for bipartite graphs. Jiang, Liu, Ren and Xu prove that a minimum feedback vertex set of a star
convex bipartite graph is NP-hard to find. Star convex bipartite graphs are recognized in
polynomial time, and a feedback vertex set is a polynomial certificate, so the restricted
problem is in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `G` is a star convex bipartite graph: its vertices split into `X` and its complement with
every edge between the two sides, and for some centre `c ∈ X` the star `starGraph c` on `X` makes
the neighbourhood of every vertex outside `X` induce a preconnected subgraph (a subtree) of it. -/
def IsStarConvex {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ X : Set V, (∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X)) ∧
    ∃ c : X, ∀ y, y ∉ X → ((SimpleGraph.starGraph c).induce {x : X | G.Adj y x}).Preconnected

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance whose graph is
star convex bipartite, with a positive bound `K`. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ IsStarConvex (Graph i) ∧ 0 < i.2.2

open Classical in
/-- FEEDBACK VERTEX SET on star convex bipartite graphs as a decision problem over bitstrings. -/
noncomputable def feedbackVertexSetStarConvexDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

/-- **FEEDBACK VERTEX SET on star convex bipartite graphs is NP-complete.** Source: Jiang, Liu,
Ren and Xu (2011); Garey and Johnson (1979), [GT7]; ISGCI, class `gc_1151`. -/
public theorem_wanted feedbackVertexSetStarConvex_npComplete :
    feedbackVertexSetStarConvexDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetStarConvexDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetStarConvex
