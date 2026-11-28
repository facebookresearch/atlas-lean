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

/-- The centroid of no points is the zero vector. -/
example : centroid (fun _ : Fin 4 => (0 : ℝ)) ∅ = 0 :=
  centroid_empty _

/-- With every point assigned to cluster `0`, the other updated center is `0`. -/
example : centers (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (0 : Fin 2)) 1 = 0 := by
  apply centers_eq_zero_of_forall_ne
  intro i
  decide

/-- Changing only an unassigned center does not change the cost. -/
example : cost (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (0 : Fin 2)) ![0, 1] =
    cost (fun _ : Fin 4 => (0 : ℝ)) (fun _ => (0 : Fin 2)) ![0, 2] := by
  apply cost_congr_centers
  intro i
  rfl

/-- The cost along a run from the `split` fixture is eventually constant. -/
example : ∃ as cs, as 0 = split ∧ cs 0 = ![0, 10] ∧ IsRun pts as cs ∧
    (∃ T, ∀ t, T ≤ t → cost pts (as t) (cs t) = cost pts (as T) (cs T)) := by
  obtain ⟨as, cs, h0, hc0, hrun⟩ := exists_run pts (by decide) split ![0, 10]
  exact ⟨as, cs, h0, hc0, hrun, hrun.exists_cost_const⟩

private def cyc : Fin 2 → ℝ := ![-1, 1]

private def alt : ℕ → Fin 2 → Fin 2 :=
  fun t => if t % 2 = 0 then (fun _ => 0) else (fun _ => 1)

private def zerocs : ℕ → Fin 2 → ℝ := fun _ => 0

/-- With all points in cluster `0`, both updated centers are `0`. -/
private theorem centers_cyc_zero : centers cyc (fun _ => (0 : Fin 2)) = 0 := by
  have h0 : centers cyc (fun _ => (0 : Fin 2)) 0 = 0 := by
    simp only [centers, centroid]
    norm_num [cyc]
  have h1 : centers cyc (fun _ => (0 : Fin 2)) 1 = 0 :=
    centers_eq_zero_of_forall_ne _ _ _ (by decide)
  funext j
  fin_cases j
  · simpa using h0
  · simpa using h1

/-- With all points in cluster `1`, both updated centers are `0`. -/
private theorem centers_cyc_one : centers cyc (fun _ => (1 : Fin 2)) = 0 := by
  have h0 : centers cyc (fun _ => (1 : Fin 2)) 0 = 0 :=
    centers_eq_zero_of_forall_ne _ _ _ (by decide)
  have h1 : centers cyc (fun _ => (1 : Fin 2)) 1 = 0 := by
    simp only [centers, centroid]
    norm_num [cyc]
  funext j
  fin_cases j
  · simpa using h0
  · simpa using h1

private theorem centers_cyc_alt (t : ℕ) : centers cyc (alt t) = 0 := by
  by_cases h : t % 2 = 0
  · simp [alt, h, centers_cyc_zero]
  · simp [alt, h, centers_cyc_one]

/-- The alternating assignments with zero centers form a run. -/
example : IsRun cyc alt zerocs := by
  intro t
  refine ⟨?_, ?_⟩
  · simp [zerocs, centers_cyc_alt]
  · intro i j
    simp [zerocs]

/-- The cycling run has cost `2` at every time. -/
example (t : ℕ) : cost cyc (alt t) (zerocs t) = 2 := by
  simp only [cost, Fin.sum_univ_two]
  norm_num [cyc, zerocs]

/-- Consecutive alternating assignments differ. -/
example (t : ℕ) : alt t ≠ alt (t + 1) := by
  by_cases h : t % 2 = 0
  · have h1 : (t + 1) % 2 ≠ 0 := by omega
    have e0 : alt t = fun _ => (0 : Fin 2) := by simp [alt, h]
    have e1 : alt (t + 1) = fun _ => (1 : Fin 2) := by simp [alt, h1]
    rw [e0, e1]
    intro heq
    have h2 := congrFun heq 0
    exact absurd h2 (by decide)
  · have h1 : (t + 1) % 2 = 0 := by omega
    have e0 : alt t = fun _ => (1 : Fin 2) := by simp [alt, h]
    have e1 : alt (t + 1) = fun _ => (0 : Fin 2) := by simp [alt, h1]
    rw [e0, e1]
    intro heq
    have h2 := congrFun heq 0
    exact absurd h2 (by decide)

#print axioms IsRun.antitone
#print axioms cost_lloyd_le
#print axioms sum_sq_eq
#print axioms sum_sq_centroid_le
#print axioms cost_centers_le
#print axioms cost_nearest_le
#print axioms exists_nearest
#print axioms exists_run
#print axioms centroid_empty
#print axioms centers_eq_zero_of_forall_ne
#print axioms cost_congr_centers
#print axioms cost_eq_sum_clusters
#print axioms IsRun.exists_cost_const

end Cslib.MachineLearning.KMeans
