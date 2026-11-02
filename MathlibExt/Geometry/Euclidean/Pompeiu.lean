/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Inversion.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **Pompeiu's theorem.** Write $XY$ for the Euclidean distance between points $X$ and $Y$ of the
Euclidean plane $\mathbb{R}^2$. Let $A$, $B$, $C$ be points of the plane with $AB = BC = CA$ and
$AB > 0$, so that $ABC$ is an equilateral triangle, and let $P$ be any point of the plane. Then
$PA \le PB + PC$, $PB \le PC + PA$ and $PC \le PA + PB$; that is, $PA$, $PB$, $PC$ are the side
lengths of a (possibly degenerate) triangle. -/
theorem pompeiu_general (A B C P : EuclideanSpace ℝ (Fin 2))
    (h_equilateral : dist A B = dist B C ∧ dist B C = dist C A)
    (h_side_pos : 0 < dist A B) :
    dist P A ≤ dist P B + dist P C ∧
      dist P B ≤ dist P C + dist P A ∧
      dist P C ≤ dist P A + dist P B := by
  obtain ⟨h1, h2⟩ := h_equilateral
  have hBC : dist B C = dist A B := h1.symm
  have hCA : dist C A = dist A B := h2.symm.trans h1.symm
  have hBA : dist B A = dist A B := dist_comm B A
  have hCB : dist C B = dist A B := (dist_comm C B).trans hBC
  have hAC : dist A C = dist A B := (dist_comm A C).trans hCA
  have key1 := EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist B A C P
  have key2 := EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist A B C P
  have key3 := EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist A C B P
  rw [hBC, hBA, hAC] at key1
  rw [hAC, hBC] at key2
  rw [hAC, hCB] at key3
  have e1 : dist A B * dist A P ≤ dist A B * (dist B P + dist C P) := by
    calc dist A B * dist A P
        ≤ dist A B * dist C P + dist A B * dist B P := key1
      _ = dist A B * (dist B P + dist C P) := by ring
  have e2 : dist A B * dist B P ≤ dist A B * (dist C P + dist A P) := by
    calc dist A B * dist B P
        ≤ dist A B * dist C P + dist A B * dist A P := key2
      _ = dist A B * (dist C P + dist A P) := by ring
  have e3 : dist A B * dist C P ≤ dist A B * (dist A P + dist B P) := by
    calc dist A B * dist C P
        ≤ dist A B * dist B P + dist A B * dist A P := key3
      _ = dist A B * (dist A P + dist B P) := by ring
  have g1 : dist A P ≤ dist B P + dist C P :=
    le_of_mul_le_mul_left e1 h_side_pos
  have g2 : dist B P ≤ dist C P + dist A P :=
    le_of_mul_le_mul_left e2 h_side_pos
  have g3 : dist C P ≤ dist A P + dist B P :=
    le_of_mul_le_mul_left e3 h_side_pos
  rw [dist_comm A P, dist_comm B P, dist_comm C P] at g1 g2 g3
  exact ⟨g1, g2, g3⟩

set_option linter.unusedVariables false in
/-- **Pompeiu's theorem for a point other than a vertex.** Write $XY$ for the Euclidean distance
between points $X$ and $Y$ of the Euclidean plane $\mathbb{R}^2$. Let $A$, $B$, $C$ be points of
the plane with $AB = BC = CA$ and $AB > 0$, so that $ABC$ is an equilateral triangle, and let $P$
be a point of the plane with $P \ne A$, $P \ne B$ and $P \ne C$. Then $PA \le PB + PC$,
$PB \le PC + PA$ and $PC \le PA + PB$; that is, $PA$, $PB$, $PC$ are the side lengths of a
(possibly degenerate) triangle.

The hypothesis that $P$ is not a vertex is not needed: the conclusion holds for every point $P$
of the plane.

Source: https://en.wikipedia.org/wiki/Pompeiu%27s_theorem (statement_id `pompeiu-s1`, proves
`Wanted` entry `pompeiu`); the vertex exclusion keeps the `Wanted` statement's shape.
-/
theorem pompeiu (A B C P : EuclideanSpace ℝ (Fin 2))
    (h_equilateral : dist A B = dist B C ∧ dist B C = dist C A)
    (h_side_pos : 0 < dist A B)
    (hP : P ≠ A ∧ P ≠ B ∧ P ≠ C) :
    dist P A ≤ dist P B + dist P C ∧
      dist P B ≤ dist P C + dist P A ∧
      dist P C ≤ dist P A + dist P B :=
  pompeiu_general A B C P h_equilateral h_side_pos

end MetaMathlibExt

end
