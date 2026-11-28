/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERSECTION GRAPH FOR SEGMENTS ON A GRID: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND46] INTERSECTION GRAPH FOR SEGMENTS ON A
GRID, p. 219, crediting F. Gavril, "Some NP-complete problems on graphs", Proceedings of the
11th Conference on Information Sciences and Systems, Johns Hopkins University, Baltimore (1977),
91-95 (transformation from 3-PARTITION).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntersectionGraphForSegmentsOnAGrid

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, `M`, `N`. -/
abbrev IntersectionGraphForSegmentsOnAGridInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IntersectionGraphForSegmentsOnAGridInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `M`, `N` are
positive. -/
def WellFormed (i : IntersectionGraphForSegmentsOnAGridInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- A grid segment `[(x, y), (z, w)]`, given by its endpoints `((x, y), (z, w))`. -/
abbrev GridSegment := (ℕ × ℕ) × (ℕ × ℕ)

/-- `[(x, y), (z, w)]` lies on the `M × N` grid: `1 ≤ x ≤ z ≤ M`, `1 ≤ y ≤ w ≤ N`, and it is
vertical (`x = z`) or horizontal (`y = w`). -/
def OnGrid (M N : ℕ) (σ : GridSegment) : Prop :=
  1 ≤ σ.1.1 ∧ σ.1.1 ≤ σ.2.1 ∧ σ.2.1 ≤ M ∧ 1 ≤ σ.1.2 ∧ σ.1.2 ≤ σ.2.2 ∧ σ.2.2 ≤ N ∧
    (σ.1.1 = σ.2.1 ∨ σ.1.2 = σ.2.2)

/-- The points of the segment `[(x, y), (z, w)]` in the real plane. -/
def segPoints (σ : GridSegment) : Set (ℝ × ℝ) :=
  SimpleGraph.Segment ((σ.1.1 : ℝ), (σ.1.2 : ℝ)) ((σ.2.1 : ℝ), (σ.2.2 : ℝ))

/-- `G` is the intersection graph of a one-to-one assignment of grid segments on the `M × N`
grid to its vertices. -/
def IntersectionGraphForSegmentsOnAGridFeasible
    (i : IntersectionGraphForSegmentsOnAGridInstance) : Prop :=
  ∃ f : Fin i.1 → GridSegment, Function.Injective f ∧ (∀ v, OnGrid i.2.2.1 i.2.2.2 (f v)) ∧
    ∀ u v, u ≠ v → ((Graph i).Adj u v ↔ (segPoints (f u) ∩ segPoints (f v)).Nonempty)

open Classical in
/-- INTERSECTION GRAPH FOR SEGMENTS ON A GRID as a decision problem over bitstrings. -/
noncomputable def intersectionGraphForSegmentsOnAGridDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntersectionGraphForSegmentsOnAGridInstance) x with
  | some i => decide (WellFormed i ∧ IntersectionGraphForSegmentsOnAGridFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntersectionGraphForSegmentsOnAGrid
