/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) on graphs of thickness at most k (fixed k ≥ 1) is
NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS, comment
("Remains NP-complete if all edge weights are equal, even if [...] G is planar [Garey and
Johnson, 1977a]");
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32(4) (1977), 826-834, doi:10.1137/0132071;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Section 3 (thickness-k graphs) and Table 1
(thickness-k graphs, unweighted STEINER TREE IN GRAPHS: NP-complete, citing Garey and Johnson).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphThicknessWanted
public import WantedExt.Complexity.NPComplete.SteinerTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeThickness

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-!
# STEINER TREE IN GRAPHS (unit weights) on graphs of thickness at most k is NP-complete

Fix an integer `k ≥ 1`.
INSTANCE: a graph `G = (V, E)` of thickness at most `k` with weight `w(e) = 1` for each
`e ∈ E`, a subset `R ⊆ V`, and a positive integer bound `B`.
QUESTION: is there a subtree of `G` that includes all the vertices of `R` and such that the sum
of the weights of the edges in the subtree (its number of edges) is no more than `B`?

Johnson (1985) defines the thickness-`k` graphs as the "graphs `G = (V, E)` where `E` can be
partitioned into sets `E₁` through `E_k` such that `Gᵢ = (V, Eᵢ)` is planar, `1 ≤ i ≤ k`", for a
fixed `k`, and lists (unweighted) STEINER TREE IN GRAPHS as NP-complete for them, citing Garey
and Johnson, who record that the equal-weight problem remains NP-complete for planar graphs
(Garey and Johnson 1977). A planar graph has thickness at most `1 ≤ k` (all edges in `E₁`), so
those instances are instances of this problem for every fixed `k ≥ 1`. Membership in NP: the
certificate is the tree together with the partition `E₁, …, E_k`; the tree is checked directly
and each `Gᵢ` by a polynomial-time planarity test.

The instance type and the question are those of
`WantedExt.Complexity.NPComplete.SteinerTreeWanted` (`SteinerTree.SteinerTreeInstance`: a vertex
count, weighted edges `(u, v, w)`, the terminals `R` and the bound `B`;
`SteinerTree.SteinerTreeFeasible`: some sublist of the edges of total weight at most `B` connects
all terminals, and a connecting edge set contains a tree of no greater weight). The restriction
is added to `WellFormed`: the parent's well-formedness, every edge weight equal to `1`, the graph
has thickness at most `k`, at least one vertex (so that a subtree exists when `R` is empty), and
`0 < B` as in [ND12]. Thickness at most `k` is the question of GRAPH THICKNESS
(`GraphThickness.GraphThicknessFeasible` from
`WantedExt.Complexity.NPComplete.GraphThicknessWanted`) for the same vertex count, the edge list
without weights, and the bound `k` (`withThickness`): the edges are split into `k` classes, each
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

/-- The GRAPH THICKNESS instance with the same vertex count, the edge list without weights, and
the bound `k`. -/
def withThickness (k : ℕ) (i : SteinerTreeInstance) : GraphThickness.GraphThicknessInstance :=
  (i.1, i.2.1.map fun e => (e.1, e.2.1), k)

/-- Well-formedness of an instance for the fixed thickness bound `k`: it is a well-formed
STEINER TREE IN GRAPHS instance, every edge has weight `1`, its graph has thickness at most `k`,
it has at least one vertex, and the bound `B` is positive. -/
def WellFormed (k : ℕ) (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    GraphThickness.GraphThicknessFeasible (withThickness k i) ∧ 0 < i.1 ∧ 0 < i.2.2.2

open Classical in
/-- STEINER TREE IN GRAPHS (unit weights) on graphs of thickness at most `k`, for the fixed `k`,
as a decision problem over bitstrings. -/
noncomputable def steinerTreeThicknessDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed k i ∧ SteinerTreeFeasible i)
  | none => false

/-- **STEINER TREE IN GRAPHS (unit weights) on graphs of thickness at most `k` is NP-complete for
every fixed `k ≥ 1`.** Source: Garey and Johnson (1979), [ND12], comment; Garey and Johnson
(1977); Johnson (1985), Table 1. -/
public theorem_wanted steinerTreeThickness_npComplete (k : ℕ) (_hk : 1 ≤ k) :
    steinerTreeThicknessDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (steinerTreeThicknessDec k)

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeThickness
