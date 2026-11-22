/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on graphs of thickness at most k (fixed k ≥ 1) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET, comment
("Remains NP-complete for cubic planar graphs [Garey, Johnson, and Stockmeyer, 1976], [Garey and
Johnson, 1977a], [Maier and Storer, 1977]");
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Section 3 (thickness-k graphs) and Table 1
(thickness-k graphs, INDEPENDENT SET: NP-complete, citing Garey and Johnson).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphThicknessWanted
public import WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetThickness

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

/-!
# INDEPENDENT SET on graphs of thickness at most k is NP-complete

Fix an integer `k ≥ 1`.
INSTANCE: a graph `G = (V, E)` of thickness at most `k` and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, i.e., a subset `V' ⊆ V` with
`|V'| ≥ K` such that no two vertices in `V'` are joined by an edge in `E`?

Johnson (1985) defines the thickness-`k` graphs as the "graphs `G = (V, E)` where `E` can be
partitioned into sets `E₁` through `E_k` such that `Gᵢ = (V, Eᵢ)` is planar, `1 ≤ i ≤ k`", for a
fixed `k`, and lists INDEPENDENT SET as NP-complete for them, citing Garey and Johnson, who
record that it remains NP-complete for cubic planar graphs. A planar graph has thickness at most
`1 ≤ k` (all edges in `E₁`), so those instances are instances of this problem for every fixed
`k ≥ 1`. Membership in NP: the certificate is `V'` together with the partition `E₁, …, E_k`;
independence is checked directly and each `Gᵢ` by a polynomial-time planarity test.

The instance (vertex count, edge list, bound `K`), the graph (`Cslib.Complexity.Karp.edgeGraph`)
and the question (`Graph.IsIndepSet` of a `Finset` of size at least `K`) are those of
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`, reused as in
`IndependentSetK14FreeWanted`; its triangle-freeness restriction is not used. The
well-formedness keeps the simple edge list and `0 < K ≤ |V|` of [GT20] and adds that the graph
has thickness at most `k`: the question of GRAPH THICKNESS
(`GraphThickness.GraphThicknessFeasible` from
`WantedExt.Complexity.NPComplete.GraphThicknessWanted`) holds for the same vertex count and
edge list with the bound `k` (`withThickness`): the edges are split into `k` classes, each
spanning a planar subgraph on all vertices, with the shared straight-line planarity predicate
`SimpleGraph.IsPlanar` (by Fáry's theorem, planarity for finite simple graphs).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The GRAPH THICKNESS instance with the same vertex count and edge list and the bound `k`. -/
def withThickness (k : ℕ) (i : TriangleFreeIndependentSetInstance) :
    GraphThickness.GraphThicknessInstance :=
  (i.1, i.2.1, k)

/-- Well-formedness of an instance for the fixed thickness bound `k`: the edge list describes a
simple graph on `Fin n` (no duplicate edges in either orientation, no self-loops, endpoints in
range), the graph has thickness at most `k`, and `0 < K ≤ |V| = n`. -/
def WellFormed (k : ℕ) (i : TriangleFreeIndependentSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    GraphThickness.GraphThicknessFeasible (withThickness k i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT SET on graphs of thickness at most `k`, for the fixed `k`, as a decision problem
over bitstrings. -/
noncomputable def independentSetThicknessDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed k i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

/-- **INDEPENDENT SET on graphs of thickness at most `k` is NP-complete for every fixed
`k ≥ 1`.** Source: Garey and Johnson (1979), [GT20], comment; Garey, Johnson and Stockmeyer
(1976); Johnson (1985), Table 1. -/
public theorem_wanted independentSetThickness_npComplete (k : ℕ) (_hk : 1 ≤ k) :
    independentSetThicknessDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (independentSetThicknessDec k)

end MetaMathlibExt.Complexity.NPComplete.IndependentSetThickness
