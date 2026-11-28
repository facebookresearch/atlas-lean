/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR POINT-SET EMBEDDABILITY: definitions

Source:
S. Cabello, "Planar embeddability of the vertices of a graph using a fixed point set is
NP-hard", Journal of Graph Algorithms and Applications 10 (2006), 353-363,
doi:10.7155/jgaa.00132 (Theorem 1).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs

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
