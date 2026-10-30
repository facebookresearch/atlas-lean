/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.KMeans
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# `k`-means tests

The reals are not computable, so the fixtures are checked by proof. On the line, points
`0, 1, 10, 11` with the split `{0, 1} | {10, 11}` have centroids `1/2` and `21/2` and cost `1`;
the centers `0` and `10` cost `2`, and the update step moves them to the centroids, cost `1`.
The assignment `{0} | {1, 10, 11}` is not nearest for the centers `1/2, 21/2`, and its cost is
higher. Two points indexed by `Bool`, one per cluster, cost `0` after the update step. Closed
checks instantiate the theorems.
-/

namespace Cslib.MachineLearning.KMeans

private def pts : Fin 4 → ℝ := ![0, 1, 10, 11]

private def split : Fin 4 → Fin 2 := ![0, 0, 1, 1]

private def bad : Fin 4 → Fin 2 := ![0, 1, 1, 1]

private theorem split0 : (Finset.univ.filter fun i : Fin 4 => split i = 0) = {0, 1} := by decide

private theorem split1 : (Finset.univ.filter fun i : Fin 4 => split i = 1) = {2, 3} := by decide

/-- The update step moves the centers to `1/2` and `21/2`. -/
theorem centers_split : centers pts split = ![1 / 2, 21 / 2] := by
  have h0 : centers pts split 0 = 1 / 2 := by
    simp only [centers, centroid, split0]
    norm_num [pts]
  have h1 : centers pts split 1 = 21 / 2 := by
    simp only [centers, centroid, split1]
    norm_num [pts]
  funext j
  fin_cases j
  · simpa using h0
  · simpa using h1

theorem cost_split : cost pts split (centers pts split) = 1 := by
  rw [centers_split]
  simp only [cost, Fin.sum_univ_four, pts, split]
  norm_num

/-- The update step improves the centers `0, 10` (cost `2`) to the centroids (cost `1`). -/
example : cost pts split ![0, 10] = 2 := by
  simp only [cost, Fin.sum_univ_four, pts, split]
  norm_num

example : cost pts split (centers pts split) ≤ cost pts split ![0, 10] :=
  cost_centers_le pts split ![0, 10]

/-- The split is nearest for its centroids. -/
theorem nearest_split : Nearest pts (centers pts split) split := by
  rw [centers_split]
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [pts, split]

/-- The assignment `{0} | {1, 10, 11}` is not nearest for the same centers, and costs more. -/
example : ¬ Nearest pts (centers pts split) bad := by
  rw [centers_split]
  intro h
  have := h 1 0
  norm_num [pts, bad] at this

example : cost pts split (centers pts split) < cost pts bad (centers pts split) := by
  rw [cost_split, centers_split]
  simp only [cost, Fin.sum_univ_four, pts, bad]
  norm_num

/-- Points may be indexed by any finite type: here `Bool`, with one point per cluster, cost `0`
after the update step. -/
example : cost (fun b : Bool => if b then (1 : ℝ) else 0) (fun b => if b then (1 : Fin 2) else 0)
    (centers (fun b : Bool => if b then (1 : ℝ) else 0) (fun b => if b then (1 : Fin 2) else 0)) =
      0 := by
  have hc : centers (fun b : Bool => if b then (1 : ℝ) else 0)
      (fun b => if b then (1 : Fin 2) else 0) = ![0, 1] := by
    funext j
    fin_cases j
    · simp [centers, centroid]
    · simp only [centers, centroid]
      simp
      decide
  rw [hc]
  simp [cost]

/-! Closed checks -/

example : ∃ as cs, as 0 = split ∧ cs 0 = ![0, 10] ∧ IsRun pts as cs :=
  exists_run pts (by decide) split ![0, 10]

#print axioms IsRun.antitone
#print axioms cost_lloyd_le
#print axioms sum_sq_eq

end Cslib.MachineLearning.KMeans
