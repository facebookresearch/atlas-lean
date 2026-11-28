/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET IN PERFECT ELIMINATION BIPARTITE GRAPHS: definitions

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

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetBipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPerfectEliminationBipartite

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet (FeedbackVertexSetInstance Graph)

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

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPerfectEliminationBipartite
