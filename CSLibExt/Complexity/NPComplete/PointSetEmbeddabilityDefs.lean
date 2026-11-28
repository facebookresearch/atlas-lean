/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs

/-!
# PLANAR POINT-SET EMBEDDABILITY: definitions

INSTANCE: a graph `G` with `n` vertices and a set `P` of `n` points in the plane. QUESTION: is
there a planar straight-line embedding of `G` whose vertices are mapped onto `P`, that is, a
bijection from the vertices to `P` such that the straight-line segments drawn for the edges
intersect only at common endpoints?

This is Cabello's Theorem 1 (a geometric planar embedding `H` of `G` with `V(H) = P`). The points
have integer coordinates in the encoding of `GeometricTravelingSalesmanDefs` (each coordinate a
pair `(a, b)` of naturals standing for `a - b`, `GeometricTravelingSalesman.point`); Cabello's
reduction outputs integer points with polynomially bounded coordinates, and rational points
reduce to integer ones by scaling, which preserves straight-line drawings. The vertices of `G` are
`0, ..., n - 1`, where `n` is the number of points, and `G` is `edgeGraph n E` for an edge list `E`.
Segments are the repository's `SimpleGraph.Segment`. For the drawing that puts vertex `v` at the
point `σ v`, the conditions are those of `RectilinearPlanarity.IsRectilinearDrawing` without
its axis-parallel clause: the crossing condition of `SimpleGraph.IsPlanar`, and no vertex
(isolated ones included) lies on an edge except at its endpoints.

Cabello proves the problem NP-complete, even for 2-connected 2-outerplanar `G` (Theorem 1, by a
reduction from 3-PARTITION); membership in NP: the bijection is a certificate, checked by
polynomially many segment intersection tests.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
S. Cabello, "Planar embeddability of the vertices of a graph using a fixed point set is
NP-hard", Journal of Graph Algorithms and Applications 10 (2006), 353-363,
doi:10.7155/jgaa.00132 (Theorem 1).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PointSetEmbeddability

open GeometricTravelingSalesman (point)

/-- An instance: the edge list of `G` and the points of `P` (pairs of encoded integers). -/
abbrev PointSetEmbeddabilityInstance := List (ℕ × ℕ) × List ((ℕ × ℕ) × (ℕ × ℕ))

/-- The graph of the instance on the vertices `0, ..., n - 1`, `n` the number of points. -/
def Graph (i : PointSetEmbeddabilityInstance) : SimpleGraph (Fin i.2.length) :=
  Cslib.Complexity.Karp.edgeGraph i.2.length i.1

/-- The position in the real plane of the `j`-th point of `P`. -/
def position (i : PointSetEmbeddabilityInstance) (j : Fin i.2.length) : ℝ × ℝ :=
  ((point (i.2.get j)).1, (point (i.2.get j)).2)

/-- Well-formedness of an instance: the points are distinct, and the edge list describes a
simple graph on the `n` vertices. -/
def WellFormed (i : PointSetEmbeddabilityInstance) : Prop :=
  (i.2.map point).Nodup ∧ i.1.Nodup ∧
    ∀ e ∈ i.1, e.1 < i.2.length ∧ e.2 < i.2.length ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.1

/-- Some bijection `σ` from the vertices onto the points gives a planar straight-line drawing:
the segments of two different edges meet only at common endpoints, and no vertex lies on the
segment of an edge other than at its own endpoints. -/
def PointSetEmbeddabilityFeasible (i : PointSetEmbeddabilityInstance) : Prop :=
  ∃ σ : Fin i.2.length ≃ Fin i.2.length,
    (∀ ⦃v w x y⦄, (Graph i).Adj v w → (Graph i).Adj x y →
      ({v, w} : Set (Fin i.2.length)) ≠ {x, y} →
      SimpleGraph.Segment (position i (σ v)) (position i (σ w)) ∩
          SimpleGraph.Segment (position i (σ x)) (position i (σ y)) ⊆
        ({position i (σ v), position i (σ w)} : Set (ℝ × ℝ)) ∩
          {position i (σ x), position i (σ y)}) ∧
    ∀ ⦃v w⦄ u, (Graph i).Adj v w →
      position i (σ u) ∈ SimpleGraph.Segment (position i (σ v)) (position i (σ w)) →
        u = v ∨ u = w

open Classical in
/-- PLANAR POINT-SET EMBEDDABILITY as a decision problem over bitstrings. -/
noncomputable def pointSetEmbeddabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PointSetEmbeddabilityInstance) x with
  | some i => decide (WellFormed i ∧ PointSetEmbeddabilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PointSetEmbeddability
