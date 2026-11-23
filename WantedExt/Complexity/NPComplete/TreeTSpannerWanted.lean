/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREE t-SPANNER (fixed t ≥ 4) is NP-complete

Source:
L. Cai and D. G. Corneil, "Tree spanners", SIAM Journal on Discrete Mathematics 8 (1995),
359-387, doi:10.1137/S0895480192237403;
I. Papoutsakis, "Tree spanners of bounded degree graphs", arXiv:1503.06822 (Section 1: the
attribution of NP-completeness for each `t ≥ 4` to Cai and Corneil, and Definition 1 of a tree
`t`-spanner used below).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreeTSpanner

/-!
# TREE t-SPANNER (fixed t ≥ 4) is NP-complete

Fix an integer `t ≥ 4`. INSTANCE: a graph `G = (V, E)`. QUESTION: does `G` have a tree
`t`-spanner, i.e. a spanning tree `T` of `G` with `d_T(u, v) ≤ t · d_G(u, v)` for all
`u, v ∈ V`?

Cai and Corneil (abstract): "A tree t-spanner T of a graph G is a spanning tree in which the
distance between every pair of vertices is at most t times their distance in G", and "For
unweighted graphs, ... determining the existence of a tree t-spanner is NP-complete for any
fixed t ≥ 4." Papoutsakis (Section 1) attributes NP-completeness for each `t ≥ 4` to Cai and
Corneil and gives the definition: "A graph T is a t-spanner of a graph G if and only if T is a
subgraph of G and, for every pair u and v of vertices of G, if u and v are at distance d from
each other in G, then u and v are at distance at most t · d from each other in T. If T is also a
tree, then T is a tree t-spanner of G."

`t` is fixed, not part of the instance: the decision problem is `treeTSpannerDec t`, and the
theorem holds for every integer `t ≥ 4`. The graph is given by an edge list on `Fin n`. A
spanning tree is a `SimpleGraph (Fin n)` below `G` (`T ≤ G`, on all vertices of `G`) that is a
tree (Mathlib's `SimpleGraph.IsTree`), and distances are Mathlib's extended distance
`SimpleGraph.edist` (in `ℕ∞`, `⊤` between vertices in different components). A graph with no
spanning tree (a disconnected graph, or the graph with no vertices) has no tree `t`-spanner.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev TreeTSpannerInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TreeTSpannerInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : TreeTSpannerInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `G` has a tree `t`-spanner: a spanning tree `T` of `G` (a tree `T ≤ G` on all vertices of
`G`) with `d_T(u, v) ≤ t · d_G(u, v)` for all `u, v`. -/
def TreeTSpannerFeasible (t : ℕ) (i : TreeTSpannerInstance) : Prop :=
  ∃ T : SimpleGraph (Fin i.1), T ≤ Graph i ∧ T.IsTree ∧
    ∀ u v, T.edist u v ≤ (t : ℕ∞) * (Graph i).edist u v

open Classical in
/-- TREE `t`-SPANNER, for the fixed `t`, as a decision problem over bitstrings. -/
noncomputable def treeTSpannerDec (t : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreeTSpannerInstance) x with
  | some i => decide (WellFormed i ∧ TreeTSpannerFeasible t i)
  | none => false

/-- **TREE t-SPANNER is NP-complete for every fixed integer `t ≥ 4`.** Source: Cai and Corneil
(1995); Papoutsakis, Section 1. -/
public theorem_wanted treeTSpanner_npComplete (t : ℕ) (_ht : 4 ≤ t) :
    treeTSpannerDec t ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (treeTSpannerDec t)

end MetaMathlibExt.Complexity.NPComplete.TreeTSpanner
