/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN CHORDAL BIPARTITE GRAPHS is NP-complete

Source:
H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal
bipartite graphs", Theoretical Computer Science 53 (1987), 257-265,
doi:10.1016/0304-3975(87)90067-3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SteinerTreeWanted
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeChordalBipartite

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-!
# STEINER TREE IN CHORDAL BIPARTITE GRAPHS is NP-complete

INSTANCE: a chordal bipartite graph `G = (V, E)` (bipartite, and every cycle of length at least
`6` has a chord), a terminal set `R ⊆ V`, and a positive integer `K`. QUESTION: is there a
subtree of `G` containing every vertex of `R` with at most `K` vertices?

This is STEINER TREE IN GRAPHS (Garey and Johnson [ND12], `SteinerTreeWanted`) with unit edge
weights, restricted to chordal bipartite graphs, whose NP-completeness Müller and Brandstädt
prove (title result; the full text was not available). A graph is chordal bipartite when it is
bipartite and each cycle of length at least `6` has a chord, an edge joining two vertices of the
cycle that is not an edge of the cycle: `IsChordalBipartite G`, with Mathlib's
`SimpleGraph.IsBipartite`, `SimpleGraph.Walk.IsCycle` and `SimpleGraph.Walk.IsChord` (exactly
that notion of chord).

The instance type and the question are those of `WantedExt.Complexity.NPComplete.SteinerTreeWanted`
(`SteinerTree.SteinerTreeInstance`: a vertex count, weighted edges `(u, v, w)`, the terminals `R`
and the bound; `SteinerTree.SteinerTreeFeasible`: some sublist of the edges of total weight at
most the bound connects all terminals). The restriction is added to `WellFormed`: the parent's
well-formedness, every edge weight equal to `1`, the graph of all edges
(`SteinerTree.Graph i i.2.1`) is chordal bipartite, at least one vertex, and `0 < K`. A tree
with at most `K` vertices has at most `K - 1` edges, and a connecting edge set with at most
`K - 1` edges contains a tree with at most `K` vertices containing `R` (a single vertex when `R`
is empty), so with unit weights the question is the parent's question with edge budget `K - 1`
(`toEdgeBudget`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `G` is chordal bipartite: bipartite, and every cycle of length at least `6` has a chord
(Mathlib's `Walk.IsChord`: an edge of `G` between two vertices of the cycle that is not an edge of
the cycle). -/
def IsChordalBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  G.IsBipartite ∧ ∀ (v : V) (c : G.Walk v v), c.IsCycle → 6 ≤ c.length → ∃ e, c.IsChord e

/-- Well-formedness of an instance: it is a well-formed STEINER TREE IN GRAPHS instance, every
edge has weight `1`, its graph is chordal bipartite, it has at least one vertex, and `K` is
positive. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    IsChordalBipartite (SteinerTree.Graph i i.2.1) ∧ 0 < i.1 ∧ 0 < i.2.2.2

/-- The parent instance with edge budget `K - 1` (a tree with at most `K` vertices has at most
`K - 1` edges). -/
def toEdgeBudget (i : SteinerTreeInstance) : SteinerTreeInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2 - 1)

open Classical in
/-- STEINER TREE IN CHORDAL BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def steinerTreeChordalBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible (toEdgeBudget i))
  | none => false

/-- **STEINER TREE IN CHORDAL BIPARTITE GRAPHS is NP-complete.** Source:
Müller and Brandstädt (1987). -/
public theorem_wanted steinerTreeChordalBipartite_npComplete :
    steinerTreeChordalBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeChordalBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeChordalBipartite
