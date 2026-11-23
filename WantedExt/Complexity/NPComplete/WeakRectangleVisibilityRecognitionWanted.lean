/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF WEAK RECTANGLE VISIBILITY GRAPHS is NP-complete

Source:
T. C. Shermer, "On rectangle visibility graphs III. External visibility and complexity", in
Proceedings of the 8th Canadian Conference on Computational Geometry (CCCG 1996), Carleton
University Press (1996), 234-239, doi:10.1515/9780773591134-041 (Section 1: the definitions of
bands of visibility, rectangle visibility graphs and weak rectangle visibility graphs used below;
Section 4, Theorem 4.5, "RVG Recognition is NP-complete", and Section 5: "RVG Recognition is
NP-complete, for weak, collinear, or noncollinear RVGs").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Prod
public import Mathlib.Order.Interval.Set.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeakRectangleVisibilityRecognition

/-!
# RECOGNITION OF WEAK RECTANGLE VISIBILITY GRAPHS is NP-complete

INSTANCE: a graph `G = (V, E)`.
QUESTION: is `G` a weak rectangle visibility graph?

Shermer (Section 1): "Let `R = {R_i}` be a collection of pairwise disjoint closed rectangles in
the plane. Two rectangles `R_i` and `R_j` will be called visible if there is a closed
non-degenerate rectangular region `B_ij` (called a band of visibility) such that one side of
`B_ij` is contained in a side of `R_i`, the opposite side of `B_ij` is contained in a side of
`R_j`, and `B_ij` does not intersect the interior of any rectangle in `R`. [...] The visibility
graph of `R` is the graph of the visibility relation on vertex-set `R`; [...] A graph is called a
rectangle visibility graph, or RVG, if it is the visibility graph of some collection `R` of
rectangles [...]. A graph is called a weak RVG if it is a subgraph of an RVG. In weak layouts we
are allowed to embed two nonadjacent vertices as rectangles that are visible." The rectangles
are aligned with the coordinate axes (ISGCI, class `gc_725`: "vertices are represented by
rectangles that are aligned with the axes and edges are horizontal or vertical lines of sight
(note that not every line of sight need to be an edge)").

Definitions:
* `Rect`: an axis-parallel rectangle given by its coordinates `(x₁, x₂, y₁, y₂)`; its closed
  region is `region = [x₁, x₂] × [y₁, y₂]` and its interior is `interiorRegion =
  (x₁, x₂) × (y₁, y₂)`; it is non-degenerate when `x₁ < x₂` and `y₁ < y₂`;
* `Rect.side r k`: the four sides of `r` (`0` left `{x₁} × [y₁, y₂]`, `1` right
  `{x₂} × [y₁, y₂]`, `2` bottom `[x₁, x₂] × {y₁}`, `3` top `[x₁, x₂] × {y₂}`), and
  `oppositeSide` pairs left with right and bottom with top;
* `IsRectangleLayout R`: `R` assigns each vertex a non-degenerate rectangle, and the closed
  rectangles of distinct vertices are disjoint;
* `IsBandOfVisibility R u v B`: `B` is a closed non-degenerate rectangle, some side of `B` is
  contained in a side of `R u` and the opposite side of `B` in a side of `R v`, and `B` meets
  the interior of no rectangle of the layout (the rectangles of `u` and `v` included). A band is
  axis-parallel because one of its sides lies in an axis-parallel side, so it is a `Rect` too;
* `IsWeakRectangleVisibilityGraph G`: some rectangle layout of the vertices of `G` has a band of
  visibility for every edge of `G`. This is "a subgraph of an RVG": the visibility graph of the
  layout is an RVG containing `G`; conversely, the rectangles that a layout of an RVG `H ⊇ G`
  assigns to the vertices of `G` form a layout in which every edge of `G` still has its band,
  since removing rectangles removes only obstacles.

The graph is given by an edge list on `Fin n` (`Cslib.Complexity.Karp.edgeGraph`). Shermer
notes that the problem is in NP "as one can guess a layout and verify it".

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev WeakRectangleVisibilityInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : WeakRectangleVisibilityInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : WeakRectangleVisibilityInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- An axis-parallel rectangle, by its coordinates `(x₁, x₂, y₁, y₂)`. -/
abbrev Rect := ℝ × ℝ × ℝ × ℝ

/-- The closed region `[x₁, x₂] × [y₁, y₂]` of a rectangle. -/
def Rect.region (r : Rect) : Set (ℝ × ℝ) :=
  Set.Icc r.1 r.2.1 ×ˢ Set.Icc r.2.2.1 r.2.2.2

/-- The interior `(x₁, x₂) × (y₁, y₂)` of a rectangle. -/
def Rect.interiorRegion (r : Rect) : Set (ℝ × ℝ) :=
  Set.Ioo r.1 r.2.1 ×ˢ Set.Ioo r.2.2.1 r.2.2.2

/-- A rectangle is non-degenerate: `x₁ < x₂` and `y₁ < y₂`. -/
def Rect.NonDegenerate (r : Rect) : Prop :=
  r.1 < r.2.1 ∧ r.2.2.1 < r.2.2.2

/-- The four sides of a rectangle: `0` left `{x₁} × [y₁, y₂]`, `1` right `{x₂} × [y₁, y₂]`,
`2` bottom `[x₁, x₂] × {y₁}`, `3` top `[x₁, x₂] × {y₂}`. -/
def Rect.side (r : Rect) : Fin 4 → Set (ℝ × ℝ) :=
  ![{r.1} ×ˢ Set.Icc r.2.2.1 r.2.2.2, {r.2.1} ×ˢ Set.Icc r.2.2.1 r.2.2.2,
    Set.Icc r.1 r.2.1 ×ˢ {r.2.2.1}, Set.Icc r.1 r.2.1 ×ˢ {r.2.2.2}]

/-- The side opposite side `k`: left and right, bottom and top. -/
def oppositeSide : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- `R` is a rectangle layout: every vertex gets a non-degenerate rectangle, and the closed
rectangles of distinct vertices are disjoint. -/
def IsRectangleLayout {V : Type*} (R : V → Rect) : Prop :=
  (∀ v, (R v).NonDegenerate) ∧ ∀ u v, u ≠ v → Disjoint (R u).region (R v).region

/-- `B` is a band of visibility between the rectangles of `u` and `v` in the layout `R`: a closed
non-degenerate rectangle such that one side of `B` is contained in a side of `R u`, the opposite
side of `B` is contained in a side of `R v`, and `B` does not intersect the interior of any
rectangle of the layout. -/
def IsBandOfVisibility {V : Type*} (R : V → Rect) (u v : V) (B : Rect) : Prop :=
  B.NonDegenerate ∧
    (∃ k, (∃ j, B.side k ⊆ (R u).side j) ∧ ∃ j, B.side (oppositeSide k) ⊆ (R v).side j) ∧
    ∀ w, Disjoint B.region (R w).interiorRegion

/-- `G` is a weak rectangle visibility graph: some rectangle layout of its vertices has a band of
visibility between the rectangles of the two ends of every edge. -/
def IsWeakRectangleVisibilityGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ R : V → Rect, IsRectangleLayout R ∧ ∀ u v, G.Adj u v → ∃ B, IsBandOfVisibility R u v B

/-- The graph of the instance is a weak rectangle visibility graph. -/
def WeakRectangleVisibilityFeasible (i : WeakRectangleVisibilityInstance) : Prop :=
  IsWeakRectangleVisibilityGraph (Graph i)

open Classical in
/-- RECOGNITION OF WEAK RECTANGLE VISIBILITY GRAPHS as a decision problem over bitstrings. -/
noncomputable def weakRectangleVisibilityRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeakRectangleVisibilityInstance) x with
  | some i => decide (WellFormed i ∧ WeakRectangleVisibilityFeasible i)
  | none => false

/-- **RECOGNITION OF WEAK RECTANGLE VISIBILITY GRAPHS is NP-complete.** Source: Shermer (1996),
Theorem 4.5 and Section 5. -/
public theorem_wanted weakRectangleVisibilityRecognition_npComplete :
    weakRectangleVisibilityRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weakRectangleVisibilityRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.WeakRectangleVisibilityRecognition
