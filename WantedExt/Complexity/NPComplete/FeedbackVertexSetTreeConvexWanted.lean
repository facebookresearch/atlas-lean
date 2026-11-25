/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET IN TREE CONVEX BIPARTITE GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET;
C. Wang, T. Liu, W. Jiang and K. Xu, "Feedback vertex sets on tree convex bipartite graphs",
Combinatorial Optimization and Applications (COCOA 2012), Lecture Notes in Computer Science 7402
(2012), 95-102, doi:10.1007/978-3-642-31770-5_9;
W. Jiang, T. Liu, T. Ren and K. Xu, "Two hardness results on feedback vertex sets", Frontiers in
Algorithmics and Algorithmic Aspects in Information and Management (FAW-AAIM 2011), Lecture Notes
in Computer Science 6681 (2011), 233-243, doi:10.1007/978-3-642-21204-8_26;
ISGCI (Information System on Graph Classes and their Inclusions), class tree convex (gc_1150),
problem Feedback vertex set: NP-complete [Wang et al. 2012], NP-complete on star convex
[Jiang et al. 2011].
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTreeConvex

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet (FeedbackVertexSetInstance Graph)

/-!
# FEEDBACK VERTEX SET IN TREE CONVEX BIPARTITE GRAPHS is NP-complete

INSTANCE: a tree convex bipartite graph `G = (V, E)` and an integer `K`
(ISGCI: "an integer k"; the parent allows `K = 0`).
QUESTION: is there a set `S` of at most `K` vertices such that every cycle of `G` contains a
vertex of `S` (`G - S` is a forest)?

This is FEEDBACK VERTEX SET (`FeedbackVertexSetWanted`, Garey and Johnson [GT7]) restricted to
tree convex bipartite graphs. ISGCI (gc_1150), following Wang et al.: "A bipartite graph
`B = (X, Y, E)` is tree convex if a tree `T = (X, F)` can be defined, such that for every vertex
`y ∈ Y`, the neighbourhood of `y` induces a subtree in `T`." Wang et al. prove FEEDBACK VERTEX SET
NP-complete on tree convex bipartite graphs (as ISGCI and Kloks, Liu and Poon, arXiv:1104.3915,
record); Jiang et al. had shown it NP-hard already on star convex bipartite graphs, the tree
convex graphs whose tree `T` is a star.

`IsTreeConvex G` states the definition for a graph on `Fin n`: there are a vertex set `X` (the
side carrying the tree; `Y` is its complement), with every edge of `G` joining `X` to its
complement (Mathlib's `SimpleGraph.IsBipartiteWith`), and a tree `T` on the vertices of `X`
(Mathlib's `SimpleGraph.IsTree`), such that for every `y ∉ X` the subgraph of `T` induced by the
neighbours of `y` is connected (`SimpleGraph.Connected` of `SimpleGraph.induce`; a connected
induced subgraph of a tree is a subtree, and as a tree it is nonempty).

The instance, the graph and the question are those of `FeedbackVertexSetWanted`, reused
unchanged: vertex count, edge list on `Fin n` and bound `K`, with `FeedbackVertexSet.WellFormed`,
`FeedbackVertexSet.Graph` and `FeedbackVertexSet.FeedbackVertexSetFeasible` (a vertex set of size
at most `K` whose complement induces an acyclic graph). The restriction adds tree convexity to
well-formedness.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `G` is a tree convex bipartite graph: for some vertex set `X` with every edge joining `X` to
its complement, there is a tree `T` on `X` in which the neighbourhood of every vertex outside `X`
induces a connected subgraph (a subtree). -/
def IsTreeConvex {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ X : Set (Fin n), G.IsBipartiteWith X Xᶜ ∧
    ∃ T : SimpleGraph X, T.IsTree ∧ ∀ y ∉ X, (T.induce {x : X | G.Adj y x}).Connected

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance whose graph is
tree convex bipartite. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ IsTreeConvex (Graph i)

open Classical in
/-- FEEDBACK VERTEX SET IN TREE CONVEX BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def feedbackVertexSetTreeConvexDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSet.FeedbackVertexSetFeasible i)
  | none => false

/-- **FEEDBACK VERTEX SET IN TREE CONVEX BIPARTITE GRAPHS is NP-complete.**
Source: Garey and Johnson (1979), [GT7];
Wang, Liu, Jiang and Xu (2012); Jiang, Liu, Ren and Xu (2011). -/
public theorem_wanted feedbackVertexSetTreeConvex_npComplete :
    feedbackVertexSetTreeConvexDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetTreeConvexDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTreeConvex
