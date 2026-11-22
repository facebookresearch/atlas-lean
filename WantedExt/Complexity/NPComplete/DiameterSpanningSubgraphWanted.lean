/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIAMETER SPANNING SUBGRAPH is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem MINIMUM DIAMETER SPANNING SUBGRAPH (decision version);
J. Plesník, "The complexity of designing a network with minimum diameter", Networks 11(1)
(1981), 77-85, doi:10.1002/net.3230110110;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND4] BOUNDED DIAMETER SPANNING TREE (the
spanning-tree analogue).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DiameterSpanningSubgraph

/-!
# DIAMETER SPANNING SUBGRAPH is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight `w(e) ∈ ℤ⁺` and a length `l(e) ∈ ℕ` for each `e ∈ E`,
a positive integer `B`, and a positive integer `K`.
QUESTION: is there a spanning subgraph `E' ⊆ E` for `G` such that the sum of the weights of the
edges in `E'` does not exceed `B` and such that the diameter of the spanning subgraph `(V, E')`,
with edge lengths `l`, is at most `K`?

This is the decision version of MINIMUM DIAMETER SPANNING SUBGRAPH of Crescenzi and Kann, the
network design problem of Plesník (1981): given a graph with edge lengths and costs, find a subgraph
that connects all the vertices and minimizes the maximum distance, subject to a budget on the total
edge cost. Plesník proves it NP-hard, even for planar graphs of maximum degree `3` and budgets that
restrict the choice to spanning trees. Membership in NP: `E'` is a certificate, checked with
shortest-path computations.

The diameter is at most `K` when every two vertices `u, v` are joined in `(V, E')` by a walk of
total length at most `K` (with non-negative lengths, a shortest walk can be taken to be a path;
a `(V, E')` with two vertices in different components has infinite diameter). With no vertices
(`n = 0`) the condition is vacuous: the empty graph counts as having diameter `0`, so such
instances are yes-instances. Walks are Mathlib `SimpleGraph.Walk`s, and the
length of a walk is the sum of `l(e)` over the edges it traverses (`walkLength`). The graph is a
simple edge list with weights and lengths (an entry `(u, v, w, l)` is the edge `{u, v}`), as in
`BoundedDiameterSpanningTreeWanted`, and `E'` is a sublist of it. Vertices are `Fin n`; when
`n` exceeds `|E| + 1` the graph is disconnected (a connected graph on `n` vertices has at least
`n - 1` edges) and every instance is a no-instance, so the binary `n` does not make certificates
long. Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list (an entry `(u, v, w, l)` is
the edge `{u, v}` with weight `w` and length `l`), the budget `B`, and the bound `K`. -/
abbrev DiameterSpanningSubgraphInstance := ℕ × List (ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ

/-- The endpoint pairs of a list of edges. -/
def endpoints (es : List (ℕ × ℕ × ℕ × ℕ)) : List (ℕ × ℕ) :=
  es.map fun e => (e.1, e.2.1)

/-- The spanning subgraph `(V, E')` on the vertices `Fin n` with edge list `E'`. -/
def spanning (i : DiameterSpanningSubgraphInstance) (E' : List (ℕ × ℕ × ℕ × ℕ)) :
    SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (endpoints E')

/-- The length `l(e)` of an edge `s`: the length of the list entry whose endpoints are the
endpoints of `s` (unique under `WellFormed`), and `0` when there is none. -/
def edgeLength (i : DiameterSpanningSubgraphInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map fun e => e.2.2.2).getD 0

/-- The length of a walk: the sum of the lengths of the edges it traverses. -/
def walkLength (i : DiameterSpanningSubgraphInstance) {G : SimpleGraph (Fin i.1)}
    {u v : Fin i.1} (p : G.Walk u v) : ℕ :=
  (p.edges.map (edgeLength i)).sum

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), every weight is
positive, and `B` and `K` are positive. -/
def WellFormed (i : DiameterSpanningSubgraphInstance) : Prop :=
  ((endpoints i.2.1).Nodup ∧
    ∀ e ∈ endpoints i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ endpoints i.2.1) ∧
    (∀ e ∈ i.2.1, 0 < e.2.2.1) ∧ 0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- Some set `E'` of edges (a sublist of the edge list) has total weight at most `B`, and in the
spanning subgraph `(V, E')` every two vertices are joined by a walk of length at most `K`. -/
def DiameterSpanningSubgraphFeasible (i : DiameterSpanningSubgraphInstance) : Prop :=
  ∃ E' : List (ℕ × ℕ × ℕ × ℕ), E'.Sublist i.2.1 ∧ (E'.map fun e => e.2.2.1).sum ≤ i.2.2.1 ∧
    ∀ u v : Fin i.1, ∃ p : (spanning i E').Walk u v, walkLength i p ≤ i.2.2.2

open Classical in
/-- DIAMETER SPANNING SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def diameterSpanningSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DiameterSpanningSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ DiameterSpanningSubgraphFeasible i)
  | none => false

/-- **DIAMETER SPANNING SUBGRAPH is NP-complete.** Source: Crescenzi and Kann, MINIMUM DIAMETER
SPANNING SUBGRAPH; Plesník (1981). -/
public theorem_wanted diameterSpanningSubgraph_npComplete :
    diameterSpanningSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L diameterSpanningSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.DiameterSpanningSubgraph
