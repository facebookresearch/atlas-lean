/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET IN PERFECT ELIMINATION BIPARTITE GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET;
T. Liu, "Restricted bipartite graphs: comparison and hardness results", Algorithmic Aspects in
Information and Management (AAIM 2014), Lecture Notes in Computer Science 8546 (2014), 241-252,
doi:10.1007/978-3-319-07956-1_22;
M. C. Golumbic and C. F. Goss, "Perfect elimination and chordal bipartite graphs", Journal of
Graph Theory 2 (1978), 155-163, doi:10.1002/jgt.3190020209 (the graph class);
ISGCI (Information System on Graph Classes and their Inclusions), class perfect elimination
bipartite (gc_122), problem Feedback vertex set: NP-complete [Liu 2014].
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FeedbackVertexSetBipartiteWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPerfectEliminationBipartite

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet (FeedbackVertexSetInstance Graph)

/-!
# FEEDBACK VERTEX SET IN PERFECT ELIMINATION BIPARTITE GRAPHS is NP-complete

INSTANCE: a perfect elimination bipartite graph `G = (V, E)` and an integer `K`
(ISGCI: "an integer k"; the parent allows `K = 0`).
QUESTION: is there a set `S` of at most `K` vertices such that every cycle of `G` contains a
vertex of `S` (`G - S` is a forest)?

This is FEEDBACK VERTEX SET (`FeedbackVertexSetWanted`, Garey and Johnson [GT7]) restricted to
perfect elimination bipartite graphs, the class of Golumbic and Goss. ISGCI (gc_122): "An edge
`(u,v)` in a bipartite graph `B` is called bisimplicial if `N(u) ∪ N(v)` induces a biclique in
`B`. For an edge ordering `e_1 … e_k` let `S_i` be the set of endpoints of `e_1 … e_i` and
`S_0 = ∅`. `e_1 … e_k` is a perfect edge elimination ordering for a bipartite graph `B = (V,E)`
if `B[V ∖ S_k]` has no edges, and each edge `e_i` is bisimplicial in `B[V ∖ S_{i-1}]`. `B` is
perfect elimination bipartite if it admits a perfect edge elimination ordering." ISGCI lists
FEEDBACK VERTEX SET on this class as NP-complete, citing Liu.

Definitions, for a graph `G` on a vertex type `V`:
* `endpoints es`: the set of endpoints of the edges in the list `es`, so `S_i` is
  `endpoints (es.take i)`;
* `IsBisimplicialIn G W u v`: `u v` is an edge of the induced subgraph `G[W]` (both ends in `W`)
  and every neighbour of `u` in `W` is adjacent to every neighbour of `v` in `W`. In a bipartite
  graph the neighbours of `u` lie on the side of `v` and the neighbours of `v` on the side of `u`,
  so this says exactly that `N(u) ∪ N(v)`, taken in `G[W]`, induces a biclique (both of its sides
  are nonempty, as `v ∈ N(u)` and `u ∈ N(v)`);
* `IsPerfectEdgeEliminationOrdering G es`: each `es[i]` is bisimplicial in `G[V ∖ S_i]` (the
  list is indexed from `0`, so `es[i]` is `e_{i+1}`), and `G[V ∖ S_k]` has no edge;
* `IsPerfectEliminationBipartite G`: `G` is bipartite and admits such an ordering.

The instance, the graph and the question are those of `FeedbackVertexSetWanted`, reused
unchanged: vertex count, edge list on `Fin n` and bound `K`, with `FeedbackVertexSet.Graph` and
`FeedbackVertexSet.FeedbackVertexSetFeasible` (a vertex set of size at most `K` whose complement
induces an acyclic graph). Well-formedness is `FeedbackVertexSetBipartite.WellFormed` (a simple
edge list and Mathlib's `SimpleGraph.IsBipartite`) plus the perfect elimination ordering.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The set of endpoints of the edges in a list. -/
def endpoints {V : Type*} (es : List (V × V)) : Set V :=
  {v | ∃ e ∈ es, v = e.1 ∨ v = e.2}

/-- `u v` is a bisimplicial edge of the induced subgraph `G[W]`: an edge with both ends in `W`
such that every neighbour of `u` in `W` is adjacent to every neighbour of `v` in `W`. -/
def IsBisimplicialIn {V : Type*} (G : SimpleGraph V) (W : Set V) (u v : V) : Prop :=
  u ∈ W ∧ v ∈ W ∧ G.Adj u v ∧ ∀ x ∈ W, ∀ y ∈ W, G.Adj u x → G.Adj v y → G.Adj x y

/-- `es` is a perfect edge elimination ordering of `G`: every `es[i]` is bisimplicial in the
subgraph induced by the vertices that are not endpoints of `es[0], …, es[i - 1]`, and no edge of
`G` avoids all endpoints of `es`. -/
def IsPerfectEdgeEliminationOrdering {V : Type*} (G : SimpleGraph V) (es : List (V × V)) :
    Prop :=
  (∀ (i : ℕ) (h : i < es.length),
      IsBisimplicialIn G (endpoints (es.take i))ᶜ es[i].1 es[i].2) ∧
    ∀ x y, x ∉ endpoints es → y ∉ endpoints es → ¬ G.Adj x y

/-- `G` is perfect elimination bipartite: bipartite, with a perfect edge elimination ordering. -/
def IsPerfectEliminationBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsBipartite ∧ ∃ es : List (V × V), IsPerfectEdgeEliminationOrdering G es

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance on a bipartite
graph (`FeedbackVertexSetBipartite.WellFormed`) whose graph is perfect elimination bipartite. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSetBipartite.WellFormed i ∧ IsPerfectEliminationBipartite (Graph i)

open Classical in
/-- FEEDBACK VERTEX SET IN PERFECT ELIMINATION BIPARTITE GRAPHS as a decision problem over
bitstrings. -/
noncomputable def feedbackVertexSetPerfectEliminationBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSet.FeedbackVertexSetFeasible i)
  | none => false

/-- **FEEDBACK VERTEX SET IN PERFECT ELIMINATION BIPARTITE GRAPHS is NP-complete.**
Source: Garey and Johnson (1979), [GT7];
Liu (2014). -/
public theorem_wanted feedbackVertexSetPerfectEliminationBipartite_npComplete :
    feedbackVertexSetPerfectEliminationBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetPerfectEliminationBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPerfectEliminationBipartite
