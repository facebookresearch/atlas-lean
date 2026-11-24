/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.LinearProgramming
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Geometry.LinearProgramming` -/

namespace MathlibExtTest.Geometry.LinearProgramming

open Matrix Set MathlibExt.Geometry.LinearProgrammingWanted.ConvexGeometry

/-! ### A worked example: maximise `3 x₀ + 5 x₁` subject to `2 x₀ + 3 x₁ ≤ 6` and `x ≥ 0` -/

/-- The worked example of §101 of O. Knill, *Some Fundamental Theorems in Mathematics*
(arXiv:1807.08416v4): two variables and one constraint. Its feasible region is the triangle with
vertices `(0, 0)`, `(3, 0)` and `(0, 2)`, and the optimum is attained at `(0, 2)`. -/
private noncomputable def triangleLP : LinearProgram 2 1 where
  c := ![3, 5]
  b := ![6]
  A := !![2, 3]

-- Test section: the definitions unfold to the expected inequalities and objective.
private theorem mem_feasible_triangleLP (x : Fin 2 → ℝ) :
    x ∈ triangleLP.feasible ↔ 2 * x 0 + 3 * x 1 ≤ 6 ∧ 0 ≤ x 0 ∧ 0 ≤ x 1 := by
  simp [LinearProgram.feasible, triangleLP, dotProduct, Pi.le_def, Fin.forall_fin_two]

private theorem objective_triangleLP (x : Fin 2 → ℝ) :
    triangleLP.objective x = 3 * x 0 + 5 * x 1 := by
  simp [LinearProgram.objective, triangleLP, dotProduct, Fin.sum_univ_two]

example : ![1, 1] ∈ triangleLP.feasible := by
  rw [mem_feasible_triangleLP]
  norm_num

example : ![3, 1] ∉ triangleLP.feasible := by
  rw [mem_feasible_triangleLP]
  norm_num

-- Test section: the public lemmas on the feasible region.
private theorem isBounded_feasible_triangleLP : Bornology.IsBounded triangleLP.feasible := by
  refine (Metric.isBounded_Icc (0 : Fin 2 → ℝ) fun _ => 3).subset fun x hx => ?_
  rw [mem_feasible_triangleLP] at hx
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp <;> linarith

example : IsCompact triangleLP.feasible :=
  triangleLP.isCompact_feasible isBounded_feasible_triangleLP

example : IsClosed triangleLP.feasible := triangleLP.isClosed_feasible

-- The midpoint of the vertices `(3, 0)` and `(0, 2)` is feasible, by convexity.
example : (1 / 2 : ℝ) • ![3, 0] + (1 / 2 : ℝ) • ![0, 2] ∈ triangleLP.feasible :=
  triangleLP.convex_feasible (by rw [mem_feasible_triangleLP]; norm_num)
    (by rw [mem_feasible_triangleLP]; norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Test section: vertex optimality. The optimum `10` is attained at a vertex, as in Knill's
-- example, where it is attained at `(0, 2)`.
example : ∃ x ∈ triangleLP.feasible, IsMaxOn triangleLP.objective triangleLP.feasible x ∧
    x ∈ extremePoints ℝ triangleLP.feasible ∧ triangleLP.objective x = 10 := by
  have h02 : ![0, 2] ∈ triangleLP.feasible := by
    rw [mem_feasible_triangleLP]
    norm_num
  obtain ⟨x, hx, hmax, hext⟩ :=
    simplex_algorithm triangleLP ⟨_, h02⟩ isBounded_feasible_triangleLP
  refine ⟨x, hx, hmax, hext, le_antisymm ?_ ?_⟩
  · rw [mem_feasible_triangleLP] at hx
    rw [objective_triangleLP]
    linarith
  · have h := isMaxOn_iff.1 hmax _ h02
    rw [objective_triangleLP, objective_triangleLP] at h
    rw [objective_triangleLP]
    norm_num at h
    exact h

/-! ### A zero objective: the extreme-point clause is what pins the solution down -/

/-- One variable, zero objective and the constraints `x ≤ 1`, `x ≥ 0`. -/
private noncomputable def segmentLP : LinearProgram 1 1 where
  c := 0
  b := ![1]
  A := !![1]

private theorem mem_feasible_segmentLP (x : Fin 1 → ℝ) :
    x ∈ segmentLP.feasible ↔ x 0 ≤ 1 ∧ 0 ≤ x 0 := by
  simp [LinearProgram.feasible, segmentLP, dotProduct, Pi.le_def]

-- Every feasible point is optimal for the zero objective.
example (x : Fin 1 → ℝ) : IsMaxOn segmentLP.objective segmentLP.feasible x :=
  isMaxOn_iff.2 fun y _ => by simp [LinearProgram.objective, segmentLP]

-- But a point of the open segment `(0, 1)` is not an extreme point of the feasible region.
private theorem eq_zero_or_eq_one_of_mem_extremePoints {x : Fin 1 → ℝ}
    (hx : x ∈ extremePoints ℝ segmentLP.feasible) : x 0 = 0 ∨ x 0 = 1 := by
  have hx' := (mem_feasible_segmentLP x).1 hx.1
  by_contra h
  rw [not_or] at h
  have h0 : 0 < x 0 := lt_of_le_of_ne hx'.2 (Ne.symm h.1)
  have h1 : x 0 < 1 := lt_of_le_of_ne hx'.1 h.2
  have hseg : x ∈ openSegment ℝ (0 : Fin 1 → ℝ) 1 := by
    refine ⟨1 - x 0, x 0, by linarith, h0, by ring, funext fun i => ?_⟩
    rw [Subsingleton.elim i 0]
    simp
  have hz : (0 : Fin 1 → ℝ) ∈ segmentLP.feasible := by
    rw [mem_feasible_segmentLP]
    norm_num
  have ho : (1 : Fin 1 → ℝ) ∈ segmentLP.feasible := by
    rw [mem_feasible_segmentLP]
    norm_num
  have := congr_fun (hx.2 hz ho hseg) 0
  simp only [Pi.zero_apply] at this
  linarith

-- So the optimal vertex given by the theorem is an endpoint of `[0, 1]`.
example : ∃ x ∈ segmentLP.feasible, IsMaxOn segmentLP.objective segmentLP.feasible x ∧
    (x 0 = 0 ∨ x 0 = 1) := by
  have hz : (0 : Fin 1 → ℝ) ∈ segmentLP.feasible := by
    rw [mem_feasible_segmentLP]
    norm_num
  have hbdd : Bornology.IsBounded segmentLP.feasible := by
    refine (Metric.isBounded_Icc (0 : Fin 1 → ℝ) 1).subset fun x hx => ?_
    rw [mem_feasible_segmentLP] at hx
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> rw [Subsingleton.elim i 0] <;> simp [hx.1, hx.2]
  obtain ⟨x, hx, hmax, hext⟩ := simplex_algorithm segmentLP ⟨0, hz⟩ hbdd
  exact ⟨x, hx, hmax, eq_zero_or_eq_one_of_mem_extremePoints hext⟩

/-! ### Boundedness is needed -/

/-- Maximise `x` subject to `x ≥ 0` only: there are no constraint rows. -/
private noncomputable def rayLP : LinearProgram 1 0 where
  c := ![1]
  b := 0
  A := 0

-- The feasible region is the unbounded ray `x ≥ 0`, and the objective has no maximiser on it.
example : ¬ ∃ x ∈ rayLP.feasible, IsMaxOn rayLP.objective rayLP.feasible x := by
  rintro ⟨x, hx, hmax⟩
  have hx1 : x + 1 ∈ rayLP.feasible :=
    ⟨fun i => i.elim0, fun i => add_nonneg (hx.2 i) zero_le_one⟩
  have h := isMaxOn_iff.1 hmax _ hx1
  norm_num [LinearProgram.objective, rayLP, dotProduct] at h

end MathlibExtTest.Geometry.LinearProgramming
