/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SPANNING TREE DELETING K EDGES is NP-complete

Source:
G. N. Frederickson and R. Solis-Oba, "Increasing the weight of minimum spanning trees",
Journal of Algorithms 33 (1999), 244-266, doi:10.1006/jagm.1999.1026 (the version in which
edge weights are fixed and edges are removed at unit cost is NP-hard);
W. Liang, "Finding the k most vital edges with respect to minimum spanning trees for fixed k",
Discrete Applied Mathematics 113 (2001), 319-327, doi:10.1016/S0166-218X(01)00189-5
(Section 1 states the problem with `|S*| = k` and records that Frederickson and Solis-Oba proved
it NP-complete);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM MINIMUM SPANNING TREE DELETING K
EDGES. -/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSpanningTreeDeletingKEdges

/-!
# MINIMUM SPANNING TREE DELETING K EDGES is NP-complete

INSTANCE: a connected graph `G = (V, E)`, a weight function `w : E → ℕ`, a number `k`, and a
positive integer `K`.
QUESTION: is there a subset `E' ⊆ E` of `k` edges and a minimum spanning tree `T` of the graph
`(V, E - E')` whose weight is at least `K`?

This is the decision version of MAXIMUM MINIMUM SPANNING TREE DELETING K EDGES in the
Crescenzi-Kann compendium ("Subset E' ⊆ E of k edges and a minimum spanning tree T in the graph
(V, E - E')", measure "Weight of T"), the `k` most vital edges problem for minimum spanning
trees, which Frederickson and Solis-Oba proved NP-hard (as recorded by Liang). The graph
`(V, E - E')` must have a spanning tree, so it is connected.

The graph is given as a list of weighted edges `(u, v, w)`, at most one per unordered pair. An
edge set is a sublist of this list; its graph is `Cslib.Complexity.Karp.edgeGraph` on its
endpoint pairs and its weight is the sum of its entries' weights. A spanning tree of an edge
list `R` is a sublist of `R` whose graph is a tree on all `n` vertices (`SimpleGraph.IsTree`),
and it is minimum when no spanning tree of `R` weighs less.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list (an entry `(u, v, w)` is the
edge `{u, v}` of weight `w`), the number `k` of edges to delete, and the bound `K`. -/
abbrev MinimumSpanningTreeDeletingKEdgesInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ

/-- The graph on `Fin n` of a list of weighted edges. -/
def edgesGraph (n : ℕ) (L : List (ℕ × ℕ × ℕ)) : SimpleGraph (Fin n) :=
  Cslib.Complexity.Karp.edgeGraph n (L.map fun e => (e.1, e.2.1))

/-- The total weight of a list of weighted edges. -/
def weight (L : List (ℕ × ℕ × ℕ)) : ℕ :=
  (L.map fun e => e.2.2).sum

/-- `T` is a spanning tree of the edge list `R` on `Fin n`: a sublist of `R` whose graph is a
tree. -/
def IsSpanningTree (n : ℕ) (R T : List (ℕ × ℕ × ℕ)) : Prop :=
  T.Sublist R ∧ (edgesGraph n T).IsTree

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is
connected, and `0 < K`. -/
def WellFormed (i : MinimumSpanningTreeDeletingKEdgesInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    (edgesGraph i.1 i.2.1).Connected ∧ 0 < i.2.2.2

/-- Some `k` edges `E'` can be deleted so that the remaining edges have a minimum spanning tree
of weight at least `K`. -/
def MinimumSpanningTreeDeletingKEdgesFeasible
    (i : MinimumSpanningTreeDeletingKEdgesInstance) : Prop :=
  ∃ D : List (ℕ × ℕ × ℕ), D.Sublist i.2.1 ∧ D.length = i.2.2.1 ∧
    ∃ T, IsSpanningTree i.1 (i.2.1.filter fun e => e ∉ D) T ∧
      (∀ T', IsSpanningTree i.1 (i.2.1.filter fun e => e ∉ D) T' → weight T ≤ weight T') ∧
        i.2.2.2 ≤ weight T

open Classical in
/-- MINIMUM SPANNING TREE DELETING K EDGES as a decision problem over bitstrings. -/
noncomputable def minimumSpanningTreeDeletingKEdgesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumSpanningTreeDeletingKEdgesInstance) x with
  | some i => decide (WellFormed i ∧ MinimumSpanningTreeDeletingKEdgesFeasible i)
  | none => false

/-- **MINIMUM SPANNING TREE DELETING K EDGES is NP-complete.** Source: Frederickson and
Solis-Oba (1999); Liang (2001); Crescenzi and Kann, MAXIMUM MINIMUM SPANNING TREE DELETING K
EDGES. -/
public theorem_wanted minimumSpanningTreeDeletingKEdges_npComplete :
    minimumSpanningTreeDeletingKEdgesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumSpanningTreeDeletingKEdgesDec

end MetaMathlibExt.Complexity.NPComplete.MinimumSpanningTreeDeletingKEdges
