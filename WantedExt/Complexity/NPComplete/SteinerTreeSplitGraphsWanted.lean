/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN SPLIT GRAPHS is NP-complete

Source:
K. White, M. Farber and W. Pulleyblank, "Steiner trees, connected domination and strongly chordal
graphs", Networks 15 (1985), 109-124, doi:10.1002/net.3230150109;
recorded in M. Illuri, P. Renjith and N. Sadagopan, "Complexity of Steiner tree in split graphs -
dichotomy results", arXiv:1511.01668 (2016), abstract.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SteinerTreeWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeSplitGraphs

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-!
# STEINER TREE IN SPLIT GRAPHS is NP-complete

INSTANCE: a connected split graph `G = (V, E)` (its vertex set partitions into a clique and an
independent set), a terminal set `R ⊆ V`, and an integer `K`. QUESTION: is there a subtree of `G`
containing every vertex of `R` with at most `K` edges?

This is STEINER TREE IN GRAPHS (Garey and Johnson [ND12], `SteinerTreeWanted`) with unit edge
weights, restricted to split graphs. White, Farber and Pulleyblank establish its NP-completeness;
Illuri, Renjith and Sadagopan (abstract) state the problem ("Given a connected graph G and a
terminal set R ⊆ V(G), Steiner tree asks for a tree that includes all of R with at most r edges")
and record that "K. White et. al has established that Steiner tree in split graphs is
NP-complete". A split graph is a graph "which can be partitioned into a clique and an independent
set" (same abstract): `IsSplitGraph G`, with Mathlib's `SimpleGraph.IsClique` and
`SimpleGraph.IsIndepSet`.

The instance type and the question are those of `WantedExt.Complexity.NPComplete.SteinerTreeWanted`
(`SteinerTree.SteinerTreeInstance`: a vertex count, weighted edges `(u, v, w)`, the terminals `R`
and the bound `K`; `SteinerTree.SteinerTreeFeasible`: some sublist of the edges of total weight at
most `K` connects all terminals). The restriction is added to `WellFormed`: the parent's
well-formedness, every edge weight equal to `1`, and the graph of all edges
(`SteinerTree.Graph i i.2.1`) is a connected split graph (the source's instances are
connected). With unit weights the total weight of an edge set is its number of edges, and a
connecting edge set contains a tree on the terminals with no more edges, so the question asks for
a subtree of `G` containing `R` with at most `K` edges (equivalently, at most `K + 1` vertices).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `G` is a split graph: some set of vertices is a clique and its complement is an independent
set. -/
def IsSplitGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ S : Set V, G.IsClique S ∧ G.IsIndepSet Sᶜ

/-- Well-formedness of an instance: it is a well-formed STEINER TREE IN GRAPHS instance, every
edge has weight `1`, and its graph is a connected split graph. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (SteinerTree.Graph i i.2.1).Connected ∧ IsSplitGraph (SteinerTree.Graph i i.2.1)

open Classical in
/-- STEINER TREE IN SPLIT GRAPHS as a decision problem over bitstrings. -/
noncomputable def steinerTreeSplitGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

/-- **STEINER TREE IN SPLIT GRAPHS is NP-complete.** Source:
White, Farber and Pulleyblank (1985). -/
public theorem_wanted steinerTreeSplitGraphs_npComplete :
    steinerTreeSplitGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeSplitGraphsDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeSplitGraphs
