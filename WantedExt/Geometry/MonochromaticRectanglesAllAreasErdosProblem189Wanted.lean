/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monochromatic rectangles of every area (Erdős Problem 189)

Erdős Problem 189: if `ℝ²` is finitely coloured, must some colour class contain the vertices of a
rectangle of every area?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.MonochromaticRectanglesAllAreasErdosProblem189Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #189, https://www.erdosproblems.com/189 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006756 (`EP-189`), dataset ulamai/UnsolvedMath v1.8.0.

A rectangle with vertices `a, b, c, d` (in order) is given by `b - a ⊥ c - b` and `d = a + (c - b)`,
with area `|ab| |bc|`; rotated rectangles are included. A colouring with `n` colours is a map to
`Fin n`. Compared with the formal-conjectures statement `ErdosProblems/189.lean` (equivalent, there
via counterclockwise convex quadrilaterals with perpendicular sides; no code imported).
-/

/-- `a b c d` are, in order, the vertices of a rectangle of area `A`: `b - a ⊥ c - b`,
`d = a + (c - b)` and `|ab| |bc| = A`. -/
def IsRectangleOfArea (a b c d : EuclideanSpace ℝ (Fin 2)) (A : ℝ) : Prop :=
  inner ℝ (b - a) (c - b) = 0 ∧ d = a + (c - b) ∧ dist a b * dist b c = A

/-- Erdős Problem 189: for every finite colouring of `ℝ²` some colour class contains the four
vertices of a rectangle of every area `A > 0`. -/
def colourClassContainsRectanglesOfEveryArea : Prop :=
  ∀ (n : ℕ) (χ : EuclideanSpace ℝ (Fin 2) → Fin n), ∃ i : Fin n, ∀ A : ℝ, 0 < A →
    ∃ a b c d : EuclideanSpace ℝ (Fin 2), χ a = i ∧ χ b = i ∧ χ c = i ∧ χ d = i ∧
      IsRectangleOfArea a b c d A

/--
Resolved false: Kovač constructed a colouring of `ℝ²` with `25` colours in which no colour class
contains the four vertices of a rectangle of area `1`; erdosproblems.com/189 lists the problem as
disproved. Source: T. F. Bloom, Erdős Problems, Problem #189, https://www.erdosproblems.com/189
(status DISPROVED (LEAN)); resolution: V. Kovač, Coloring and density theorems for configurations of
a given volume, Proc. London Math. Soc. 132 (2026), arXiv:2309.09973, abstract and
erdosproblems.com/189: a colouring of ℝ² with 25 colours and no monochromatic rectangle of area 1,
https://doi.org/10.1112/plms.70143.
-/
public theorem_wanted colourClassContainsRectanglesOfEveryArea_refuted :
    ¬ colourClassContainsRectanglesOfEveryArea

end MathlibExt.Geometry.MonochromaticRectanglesAllAreasErdosProblem189Wanted
