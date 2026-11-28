/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERSECTION GRAPH FOR RECTANGLES ON A GRID: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND46] INTERSECTION GRAPH FOR SEGMENTS ON A
GRID, p. 219 (comment: "The analogous problem, which asks if `G` is the intersection graph for a
set of rectangles on an `M × N` grid, is also NP-complete [Gavril, 1977a]"), crediting
F. Gavril, "Some NP-complete problems on graphs", Proceedings of the 11th Conference on
Information Sciences and Systems, Johns Hopkins University, Baltimore (1977), 91-95.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import CSLibExt.Complexity.NPComplete.IntersectionGraphForSegmentsOnAGridDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntersectionGraphForRectanglesOnAGrid

open MetaMathlibExt.Complexity.NPComplete.IntersectionGraphForSegmentsOnAGrid
  (IntersectionGraphForSegmentsOnAGridInstance Graph)

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

end MetaMathlibExt.Complexity.NPComplete.IntersectionGraphForRectanglesOnAGrid
