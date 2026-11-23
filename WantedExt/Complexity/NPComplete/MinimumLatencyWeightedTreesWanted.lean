/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM LATENCY ON WEIGHTED TREES is NP-complete

Source:
R. Sitters, "The minimum latency problem is NP-hard for weighted trees", Integer Programming
and Combinatorial Optimization (IPCO 2002), LNCS 2337, 230-239,
doi:10.1007/3-540-47867-1_17, Corollary 2 (ii).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumLatencyWeightedTrees

/-!
# MINIMUM LATENCY ON WEIGHTED TREES is NP-complete

INSTANCE: a tree `T = (V, E)` with a length `l(e) ∈ ℤ⁺` for each edge `e ∈ E`, a root `r ∈ V`,
and a bound `K`. QUESTION: is there a walk in `T` that starts at `r` and visits every vertex
whose total latency, the sum over all vertices `v` of the arrival time at `v` (the length of the
walk from `r` up to its first visit of `v`), is at most `K`?

This is the minimum latency (traveling repairman) problem for the metric of an edge-weighted
tree, in decision form: Sitters (2002) defines the arrival time at a point as the distance
traveled from the origin until the point is reached, and proves the problem strongly NP-hard for
edge-weighted trees in which every vertex has weight `1` and every edge length is an integer at
least `1` (Corollary 2 (ii); Theorem 1 is the vertex-weighted form). The arrival time of the
root is `0`. A tour in the tree metric is a walk in the tree, so the tour is given as a
`SimpleGraph.Walk` from the root; it need not return to the root, which does not change any
arrival time. Some optimal walk follows, for an order of the vertices, the tree path between
consecutive ones, so it has fewer than `n²` edges and a certificate of polynomial size exists.
The parent problem on general metrics is
`WantedExt.Complexity.NPComplete.TravelingRepairmanWanted`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list with lengths (an entry
`(u, v, l)` is the edge `{u, v}` of length `l`), the root `r`, and the bound `K`. -/
abbrev MinimumLatencyWeightedTreesInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinimumLatencyWeightedTreesInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1.map fun e => (e.1, e.2.1))

/-- The length of an edge `s`: the length recorded for the list entry whose endpoints are the
endpoints of `s` (unique under `WellFormed`). -/
def edgeLength (i : MinimumLatencyWeightedTreesInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map fun e => e.2.2).getD 0

/-- The total length of a walk (the sum of the lengths of its edges). -/
def walkLength (i : MinimumLatencyWeightedTreesInstance) {u v : Fin i.1}
    (W : (Graph i).Walk u v) : ℕ :=
  (W.edges.map (edgeLength i)).sum

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) with positive edge
lengths, that graph is a tree, and the root is a vertex. -/
def WellFormed (i : MinimumLatencyWeightedTreesInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    (∀ e ∈ i.2.1, 1 ≤ e.2.2) ∧ (Graph i).IsTree ∧ i.2.2.1 < i.1

/-- Some walk `W` from the root visits every vertex, and the sum over all vertices `u` of the
length of `W.takeUntil u` (the prefix of `W` up to its first visit of `u`) is at most `K`. -/
def MinimumLatencyWeightedTreesFeasible (i : MinimumLatencyWeightedTreesInstance) : Prop :=
  ∃ r : Fin i.1, (r : ℕ) = i.2.2.1 ∧ ∃ v : Fin i.1, ∃ W : (Graph i).Walk r v,
    ∃ hW : ∀ u, u ∈ W.support, ∑ u, walkLength i (W.takeUntil u (hW u)) ≤ i.2.2.2

open Classical in
/-- MINIMUM LATENCY ON WEIGHTED TREES as a decision problem over bitstrings. -/
noncomputable def minimumLatencyWeightedTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumLatencyWeightedTreesInstance) x with
  | some i => decide (WellFormed i ∧ MinimumLatencyWeightedTreesFeasible i)
  | none => false

/-- **MINIMUM LATENCY ON WEIGHTED TREES is NP-complete.** Source: Sitters (2002),
Corollary 2 (ii). -/
public theorem_wanted minimumLatencyWeightedTrees_npComplete :
    minimumLatencyWeightedTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumLatencyWeightedTreesDec

end MetaMathlibExt.Complexity.NPComplete.MinimumLatencyWeightedTrees
