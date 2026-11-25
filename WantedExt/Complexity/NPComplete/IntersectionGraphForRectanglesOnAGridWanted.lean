/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERSECTION GRAPH FOR RECTANGLES ON A GRID is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND46] INTERSECTION GRAPH FOR SEGMENTS ON A
GRID, p. 219 (comment: "The analogous problem, which asks if `G` is the intersection graph for a
set of rectangles on an `M × N` grid, is also NP-complete [Gavril, 1977a]"), crediting
F. Gavril, "Some NP-complete problems on graphs", Proceedings of the 11th Conference on
Information Sciences and Systems, Johns Hopkins University, Baltimore (1977), 91-95.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import WantedExt.Complexity.NPComplete.IntersectionGraphForSegmentsOnAGridWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntersectionGraphForRectanglesOnAGrid

open MetaMathlibExt.Complexity.NPComplete.IntersectionGraphForSegmentsOnAGrid
  (IntersectionGraphForSegmentsOnAGridInstance Graph)

/-!
# INTERSECTION GRAPH FOR RECTANGLES ON A GRID is NP-complete

INSTANCE: a graph `G = (V, E)` and positive integers `M`, `N`.
QUESTION: is `G` the intersection graph for a set of rectangles on an `M × N` grid, i.e. is
there a one-to-one function `f` that maps each `v ∈ V` to a rectangle
`f(v) = [(x, y), (z, w)]` with corners on the grid, `1 ≤ x ≤ z ≤ M` and `1 ≤ y ≤ w ≤ N`, such
that `{u, v} ∈ E` if and only if the rectangles `f(u)` and `f(v)` intersect?

This is the analogous problem in the comment of [ND46]
(`IntersectionGraphForSegmentsOnAGridWanted`): Garey and Johnson's question for segments, with
the segments replaced by rectangles. The instance type, `IntersectionGraphForSegmentsOnAGrid.Graph`
and `IntersectionGraphForSegmentsOnAGrid.WellFormed` (simple edge list, `M` and `N` positive) are
reused unchanged. A rectangle is given by its lower-left corner `(x, y)` and its upper-right
corner `(z, w)` with the coordinate bounds of the segment version, without its condition that
`x = z` or `y = w`; its points are the closed axis-parallel rectangle `[x, z] × [y, w]`, the
order interval `Set.Icc (x, y) (z, w)` of `ℝ × ℝ` (as in `BoxicityTwoWanted`). As for segments,
whose bounds allow a single point, degenerate rectangles (`x = z` or `y = w`) are allowed. Two
rectangles intersect when they share a point; the "if and only if" is required for distinct
vertices `u ≠ v` (a rectangle always meets itself, while the graph has no loops).

Membership in NP with the vertex count `n` in binary: only the vertices incident to an edge
(at most `2|E|`) need rectangles in a certificate. An isolated vertex can always take a single
grid point covered by no other rectangle, and in any representation the rectangles of the
isolated vertices are pairwise disjoint and meet no other rectangle, so each contains a grid
point (its corner `(x, y)`) on no other rectangle. So the instance is a yes-instance iff some
placement of the non-isolated vertices leaves at least as many uncovered points of the `M × N`
grid as there are isolated vertices, and that count is computed in polynomial time from the at
most `2|E|` rectangles by coordinate compression.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The rectangle `[(x, y), (z, w)]`, given by its corners `((x, y), (z, w))`, lies on the
`M × N` grid: `1 ≤ x ≤ z ≤ M` and `1 ≤ y ≤ w ≤ N`. -/
def RectOnGrid (M N : ℕ) (ρ : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  1 ≤ ρ.1.1 ∧ ρ.1.1 ≤ ρ.2.1 ∧ ρ.2.1 ≤ M ∧ 1 ≤ ρ.1.2 ∧ ρ.1.2 ≤ ρ.2.2 ∧ ρ.2.2 ≤ N

/-- The points of the rectangle `[(x, y), (z, w)]` in the real plane: `[x, z] × [y, w]`. -/
def rectPoints (ρ : (ℕ × ℕ) × (ℕ × ℕ)) : Set (ℝ × ℝ) :=
  Set.Icc ((ρ.1.1 : ℝ), (ρ.1.2 : ℝ)) ((ρ.2.1 : ℝ), (ρ.2.2 : ℝ))

/-- `G` is the intersection graph of a one-to-one assignment of rectangles on the `M × N` grid
to its vertices. -/
def IntersectionGraphForRectanglesOnAGridFeasible
    (i : IntersectionGraphForSegmentsOnAGridInstance) : Prop :=
  ∃ f : Fin i.1 → (ℕ × ℕ) × (ℕ × ℕ), Function.Injective f ∧
    (∀ v, RectOnGrid i.2.2.1 i.2.2.2 (f v)) ∧
    ∀ u v, u ≠ v → ((Graph i).Adj u v ↔ (rectPoints (f u) ∩ rectPoints (f v)).Nonempty)

open Classical in
/-- INTERSECTION GRAPH FOR RECTANGLES ON A GRID as a decision problem over bitstrings. -/
noncomputable def intersectionGraphForRectanglesOnAGridDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntersectionGraphForSegmentsOnAGridInstance) x with
  | some i => decide (IntersectionGraphForSegmentsOnAGrid.WellFormed i ∧
      IntersectionGraphForRectanglesOnAGridFeasible i)
  | none => false

/-- **INTERSECTION GRAPH FOR RECTANGLES ON A GRID is NP-complete.** Source: Garey and Johnson
(1979), [ND46], comment; Gavril (1977). -/
public theorem_wanted intersectionGraphForRectanglesOnAGrid_npComplete :
    intersectionGraphForRectanglesOnAGridDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L intersectionGraphForRectanglesOnAGridDec

end MetaMathlibExt.Complexity.NPComplete.IntersectionGraphForRectanglesOnAGrid
