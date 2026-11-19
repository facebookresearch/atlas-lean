/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF B0-CPG GRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY, the problem
restricted here;
Z. Deniz, E. Galby, A. Munaro and B. Ries, "On contact graphs of paths on a grid", Graph Drawing
and Network Visualization (GD 2018), Lecture Notes in Computer Science 11282 (2018), 317-330,
doi:10.1007/978-3-030-04414-5_22, Theorem 5 (arXiv:1803.03468).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityB0CPG

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# 3-COLORABILITY OF B0-CPG GRAPHS is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is a `B_0`-CPG graph.
QUESTION: is `G` 3-colorable, i.e. is there a map `c : V → {1, 2, 3}` with `c(u) ≠ c(v)` for
every edge `uv`?

Deniz, Galby, Munaro and Ries define: "A graph `G` is a CPG graph if the vertices of `G` can be
represented by a family of interiorly disjoint paths on a grid, two vertices being adjacent in
`G` if and only if the corresponding paths touch, i.e. share a grid-point which is an endpoint of
at least one of the two paths"; "An interior point of a path `P` on `G` is a point belonging to
`P` and different from its endpoints"; and a `B_k`-CPG graph is one with such a representation
in which every path has at most `k` bends (ISGCI class `gc_1337` for `k = 0`). They prove that
3-COLORABILITY is NP-complete on `B_0`-CPG graphs (Theorem 5).

Formalization. A path with no bend is a straight horizontal or vertical segment of the grid
between two distinct grid points: path `v` runs from `A v` to `B v` in `ℤ × ℤ`, the two points
share a coordinate, and the path is the closed segment `segment ℝ` between them in `ℝ × ℝ`; its
interior is the segment without its two endpoints. A path on a grid has two endpoints and runs
along at least one grid edge, so the endpoints are distinct; degenerate one-point paths would let
any number of vertices touch at one grid point (every complete graph would be representable),
which the source's class excludes (its graphs are 4-colorable). `IsB0CPGRepresentation` states the
three conditions of the definition: straight nondegenerate grid paths, pairwise disjoint
interiors, and adjacency of distinct vertices exactly when their paths share a grid point that is
an endpoint of one of them.

This is GRAPH K-COLORABILITY (Garey and Johnson [GT4], `GraphColoringWanted`) with `K = 3`
restricted to `B_0`-CPG graphs. The instance type, the graph and the question are those of
`GraphColoringWanted`, reused unchanged: vertex count, edge list on `Fin n` and bound `K`, with
`GraphColoring.WellFormed`, `GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible`
(`(Graph i).Colorable K`). The restriction adds `K = 3` and the existence of a `B_0`-CPG
representation to well-formedness. A representation is a certificate of polynomial size after
replacing the coordinates by their ranks, which preserves every condition.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A grid point `p ∈ ℤ × ℤ` as a point of the plane `ℝ × ℝ`. -/
def gridPoint (p : ℤ × ℤ) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

/-- The path of vertex `v`: the closed straight segment from `A v` to `B v`. -/
def gridPath {n : ℕ} (A B : Fin n → ℤ × ℤ) (v : Fin n) : Set (ℝ × ℝ) :=
  segment ℝ (gridPoint (A v)) (gridPoint (B v))

/-- The interior of the path of vertex `v`: its points other than its two endpoints. -/
def pathInterior {n : ℕ} (A B : Fin n → ℤ × ℤ) (v : Fin n) : Set (ℝ × ℝ) :=
  gridPath A B v \ {gridPoint (A v), gridPoint (B v)}

/-- `A`, `B` give a `B_0`-CPG representation of `G`: every path is a straight horizontal or
vertical grid segment between two distinct grid points (no bend), distinct paths have disjoint
interiors, and two distinct vertices are adjacent exactly when their paths touch, i.e. share a
grid point that is an endpoint of at least one of the two paths. -/
def IsB0CPGRepresentation {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Fin n → ℤ × ℤ) : Prop :=
  (∀ v, A v ≠ B v ∧ ((A v).1 = (B v).1 ∨ (A v).2 = (B v).2)) ∧
    (∀ u v, u ≠ v → Disjoint (pathInterior A B u) (pathInterior A B v)) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ ∃ p : ℤ × ℤ, gridPoint p ∈ gridPath A B u ∧
      gridPoint p ∈ gridPath A B v ∧ (p = A u ∨ p = B u ∨ p = A v ∨ p = B v))

/-- `G` is a `B_0`-CPG graph: it has a `B_0`-CPG representation. -/
def IsB0CPG {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ A B : Fin n → ℤ × ℤ, IsB0CPGRepresentation G A B

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `K = 3`
whose graph is a `B_0`-CPG graph. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧ IsB0CPG (Graph i)

open Classical in
/-- 3-COLORABILITY OF B0-CPG GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityB0CPGDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **3-COLORABILITY OF B0-CPG GRAPHS is NP-complete.** Source: Garey and Johnson (1979), [GT4];
Deniz, Galby, Munaro and Ries (2018), Theorem 5. -/
public theorem_wanted threeColorabilityB0CPG_npComplete :
    threeColorabilityB0CPGDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilityB0CPGDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityB0CPG
