/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.PascalPappus
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Matrix MathlibExt.Geometry.PascalPappusWanted.Geometry.PascalPappus

namespace PascalPappusTest

private def parabola : Matrix (Fin 3) (Fin 3) ℝ := !![2, 0, 0; 0, 0, -1; 0, -1, 0]

private def point (s : ℝ) : Fin 3 → ℝ := ![s, s ^ 2, 1]

private theorem point_ne_zero (s : ℝ) : point s ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 2)

private theorem on_parabola (s : ℝ) : OnConic parabola (point s) := by
  simp [OnConic, parabola, point, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem samePoint_iff (s t : ℝ) : SamePoint (point s) (point t) ↔ s = t := by
  constructor
  · rintro ⟨c, _, h⟩
    have hc : 1 = c := by simpa [point] using congrFun h 2
    simpa [point, ← hc] using (congrFun h 0).symm
  · rintro rfl
    exact ⟨1, one_ne_zero, (one_smul ℝ _).symm⟩

-- All six vertices are finite. Each pair of opposite chords has the same slope.
example : Collinear3 (meet (point 0) (point 4) (point 1) (point 3))
    (meet (point 0) (point 5) (point 2) (point 3))
    (meet (point 1) (point 5) (point 2) (point 4)) := by
  apply pascal (M := parabola)
  · apply IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · norm_num [parabola, det_fin_three]
  all_goals first
    | exact point_ne_zero _
    | exact on_parabola _
    | norm_num [List.pairwise_cons, samePoint_iff]

-- The three intersection vectors represent distinct points on the line at infinity.
example :
    meet (point 0) (point 4) (point 1) (point 3) = ![24, 96, 0] ∧
    meet (point 0) (point 5) (point 2) (point 3) = ![30, 150, 0] ∧
    meet (point 1) (point 5) (point 2) (point 4) = ![24, 144, 0] := by
  norm_num [meet, point, cross_apply]

end PascalPappusTest
