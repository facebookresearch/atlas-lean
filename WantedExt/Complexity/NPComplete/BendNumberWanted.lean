/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BEND NUMBER is NP-complete

Source:
A. Garg and R. Tamassia, "On the computational complexity of upward and rectilinear planarity
testing", SIAM Journal on Computing 31 (2001), 601-625, doi:10.1137/S0097539794277123;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry [ND64]
MINIMUM BEND NUMBER.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.RectilinearPlanarityWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BendNumber

/-!
# BEND NUMBER is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`.
QUESTION: is there a planar orthogonal drawing of `G`, a drawing mapping the vertices of `G` to
points in the plane and the edges of `G` to chains of horizontal and vertical segments such that
no two edges cross, with at most `K` bends?

This is the decision version of Crescenzi and Kann's MINIMUM BEND NUMBER [ND64]. Garg and
Tamassia (abstract) prove that RECTILINEAR PLANARITY TESTING, whether a graph "can be drawn in the
plane such that every edge is a horizontal or vertical segment and no two edges cross", is
NP-complete (`RectilinearPlanarityWanted`), and "that it is NP-hard to approximate the minimum
number of bends in a planar orthogonal drawing of an n-vertex graph with an `O(n^{1-ε})` error for
any `ε > 0`". Hardness for every fixed positive bound follows from rectilinear planarity: a
triangle needs exactly one bend, and drawings of disjoint components can be placed apart, so `G`
is rectilinear planar exactly when `G` plus `K` disjoint triangles has a drawing with at most `K`
bends.

Drawings with bends are stated through subdivisions. Place a new vertex at every bend of an
orthogonal drawing: the chain of each edge becomes a path of straight horizontal or vertical
segments, so the drawing is a rectilinear planar drawing
(`RectilinearPlanarity.IsRectilinearDrawing`) of the graph obtained by subdividing every edge `e`
with `k_e` new vertices, where `k_e` is the number of bends of `e`. Conversely, in a rectilinear
planar drawing of such a subdivision, the path of each edge is a chain of horizontal and vertical
segments, no two chains cross, and every bend of a chain is at one of its new vertices, so the
drawing has at most `∑ k_e` bends (a new vertex where the chain goes straight on is not a bend).
Hence `G` has a planar orthogonal drawing with at most `K` bends exactly when for some counts `k_e`
with `∑ k_e ≤ K` the subdivision is rectilinear planar.

Encoding: the graph is given by its vertex count `n` (vertices `0, …, n - 1`) and an edge list,
well-formed as in `RectilinearPlanarityWanted` (a simple edge list). For counts `ks` (one per
listed edge) the subdivision has vertices `0, …, n + ∑ ks - 1`: the `k = ks[j]` new vertices of
edge `j = (u, v)` are `o, …, o + k - 1` with `o = n + ks[0] + … + ks[j - 1]`, and the edge is
replaced by the path `u, o, …, o + k - 1, v` (`subdivisionEdges`). Crescenzi and Kann list the
input as a directed planar graph; edge directions play no part in orthogonal drawings, and a
graph with an orthogonal drawing is planar, so stating the problem over all graphs, as
`RectilinearPlanarityWanted` does, gives the same language. `K` is a positive integer, as in the
catalog's decision problem.
The instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count, edge list, bound `K` on the number of bends. -/
abbrev BendNumberInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: a simple edge list on the vertices `0, …, n - 1`, and
`0 < K`. -/
def WellFormed (i : BendNumberInstance) : Prop :=
  RectilinearPlanarity.WellFormed (i.1, i.2.1) ∧ 0 < i.2.2

/-- The path replacing the edge `(u, v)` when it is subdivided by the `k` new vertices
`o, …, o + k - 1`: the edges `(u, o), (o, o + 1), …, (o + k - 1, v)`, or `(u, v)` when
`k = 0`. -/
def chain (u v o k : ℕ) : List (ℕ × ℕ) :=
  (u :: (List.range k).map (o + ·)).zip ((List.range k).map (o + ·) ++ [v])

/-- The edge list of the subdivision of the instance's graph in which edge `j` gets `ks[j]` new
vertices, numbered consecutively from `n`. -/
def subdivisionEdges (i : BendNumberInstance) (ks : List ℕ) : List (ℕ × ℕ) :=
  (List.range i.2.1.length).flatMap fun j =>
    chain (i.2.1.getD j (0, 0)).1 (i.2.1.getD j (0, 0)).2 (i.1 + (ks.take j).sum) (ks.getD j 0)

/-- The graph has a planar orthogonal drawing with at most `K` bends: for some numbers of new
vertices per edge, of total at most `K`, the subdivision has a rectilinear planar drawing. -/
def BendNumberFeasible (i : BendNumberInstance) : Prop :=
  ∃ ks : List ℕ, ks.length = i.2.1.length ∧ ks.sum ≤ i.2.2 ∧
    RectilinearPlanarity.RectilinearPlanarityFeasible (i.1 + ks.sum, subdivisionEdges i ks)

open Classical in
/-- BEND NUMBER as a decision problem over bitstrings. -/
noncomputable def bendNumberDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BendNumberInstance) x with
  | some i => decide (WellFormed i ∧ BendNumberFeasible i)
  | none => false

/-- **BEND NUMBER is NP-complete.** Source: Garg and Tamassia (2001); Crescenzi and Kann,
[ND64]. -/
public theorem_wanted bendNumber_npComplete :
    bendNumberDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bendNumberDec

end MetaMathlibExt.Complexity.NPComplete.BendNumber
