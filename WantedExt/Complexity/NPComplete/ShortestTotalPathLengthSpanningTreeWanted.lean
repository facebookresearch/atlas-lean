/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST TOTAL PATH LENGTH SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND3] SHORTEST TOTAL
PATH LENGTH SPANNING TREE;
D. S. Johnson, J. K. Lenstra, and A. H. G. Rinnooy Kan, "The complexity of the
network design problem", Networks 8 (1978), 279-285, doi:10.1002/net.3230080402.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestTotalPathLengthSpanningTree

/-!
# SHORTEST TOTAL PATH LENGTH SPANNING TREE is NP-complete

INSTANCE: a graph `G = (V, E)` and an integer bound `B ∈ ℤ⁺`.
QUESTION: is there a spanning tree `T` for `G` such that the sum, over all pairs of vertices
`u, v ∈ V`, of the length of the path in `T` from `u` to `v` is no more than `B`?

(Garey and Johnson name the bound `B` in the instance and `K` in the question; it is the same
number.) The graph is unweighted: the length of a path is its number of edges, which in a tree
is `T.dist u v`. Each unordered pair `{u, v}` of distinct vertices is counted once (pairs with
`u = v` contribute `0`). A spanning tree for `G` is a Mathlib `SimpleGraph.IsTree` on all of
`V` with `T ≤ G`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, and the bound `B`. -/
abbrev ShortestTotalPathLengthSpanningTreeInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ShortestTotalPathLengthSpanningTreeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `B` is
positive. -/
def WellFormed (i : ShortestTotalPathLengthSpanningTreeInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- The total path length of `T`: the sum of `T.dist u v` over unordered pairs `{u, v}` of
distinct vertices (each pair once, as `u < v`). -/
noncomputable def totalPathLength {n : ℕ} (T : SimpleGraph (Fin n)) : ℕ :=
  ∑ u : Fin n, ∑ v ∈ Finset.univ.filter (u < ·), T.dist u v

/-- A spanning tree `T ≤ G` whose total path length is at most `B`. -/
def ShortestTotalPathLengthSpanningTreeFeasible
    (i : ShortestTotalPathLengthSpanningTreeInstance) : Prop :=
  ∃ T : SimpleGraph (Fin i.1), T ≤ Graph i ∧ T.IsTree ∧ totalPathLength T ≤ i.2.2

open Classical in
/-- SHORTEST TOTAL PATH LENGTH SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def shortestTotalPathLengthSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestTotalPathLengthSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ ShortestTotalPathLengthSpanningTreeFeasible i)
  | none => false

/-- **SHORTEST TOTAL PATH LENGTH SPANNING TREE is NP-complete.** Source: Garey and Johnson
(1979), [ND3]; Johnson, Lenstra, and Rinnooy Kan (1978). -/
public theorem_wanted shortestTotalPathLengthSpanningTree_npComplete :
    shortestTotalPathLengthSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestTotalPathLengthSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.ShortestTotalPathLengthSpanningTree
