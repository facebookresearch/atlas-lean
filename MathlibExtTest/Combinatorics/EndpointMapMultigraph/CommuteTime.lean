/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.CommuteTime

@[expose] public section

namespace EndpointMapMultigraphCommuteTimeTest

open EndpointMapMultigraph Matrix

/-- The path `0 - 1 - 2`. -/
abbrev e₁ : Fin 2 → Fin 3 := ![0, 1]
/-- Second endpoints of the path `0 - 1 - 2`. -/
abbrev e₂ : Fin 2 → Fin 3 := ![1, 2]

theorem connected : (underlyingGraph e₁ e₂).Connected := by
  have h01 := (underlyingGraph_adj_of_ne e₁ e₂ (e := 0) (by decide)).reachable
  have h12 := (underlyingGraph_adj_of_ne e₁ e₂ (e := 1) (by decide)).reachable
  refine ⟨fun u v => ?_⟩
  fin_cases u <;> fin_cases v
  all_goals first
    | exact SimpleGraph.Reachable.refl _
    | exact h01 | exact h12 | exact h01.symm | exact h12.symm
    | exact h01.trans h12 | exact (h01.trans h12).symm

/-- Weighted degrees on the path are `1, 2, 1`. -/
example : weightedDegree e₁ e₂ (fun _ => 1) 1 = 2 := by
  simp [weightedDegree, Fin.sum_univ_two]; norm_num

/-- Expected hitting times of `2` for simple random walk on the path: `(4, 3, 0)`. -/
theorem hit2 : IsHittingTimeSolution e₁ e₂ (fun _ => 1) 2 ![4, 3, 0] := by
  refine ⟨rfl, fun x hx => ?_⟩
  fin_cases x <;> simp_all [weightedDegree, neighbourSum, Fin.sum_univ_two] <;> norm_num

/-- Expected hitting times of `0`: `(0, 3, 4)`. -/
theorem hit0 : IsHittingTimeSolution e₁ e₂ (fun _ => 1) 0 ![0, 3, 4] := by
  refine ⟨rfl, fun x hx => ?_⟩
  fin_cases x <;> simp_all [weightedDegree, neighbourSum, Fin.sum_univ_two] <;> norm_num

/-- The commute time `4 + 4 = 8` between the ends of the path equals `2 |E| R_eff = 2 · 2 · 2`,
recovering the series resistance `R_eff(0, 2) = 2`. -/
example : effectiveResistance e₁ e₂ (fun _ => 1) 0 2 = 2 := by
  have h := commute_time_identity_one e₁ e₂ (by decide) connected hit0 hit2
  simp at h
  linarith

/-- The Laplacian formula `(L h)(x) = π(x) h(x) - ∑ w_e h(neighbour)` at the middle vertex. -/
example : (laplacian e₁ e₂ (fun _ => 1) *ᵥ ![4, 3, 0]) 1 = 2 := by
  rw [laplacian_mulVec_apply]
  simp [weightedDegree, neighbourSum, Fin.sum_univ_two]; norm_num

/-- `γ = ∑ π(x) = 2 |E| = 4` on the path. -/
example : ∑ x, weightedDegree e₁ e₂ (fun _ => (1 : ℝ)) x = 4 := by
  rw [sum_weightedDegree]; simp; norm_num

/-- The potential `(2, 1, 0)` of a unit current from `0` to `2`. -/
theorem laplacian_mulVec_210 :
    laplacian e₁ e₂ (fun _ => 1) *ᵥ ![2, 1, 0] = Pi.single 0 1 - Pi.single 2 1 := by
  funext x
  fin_cases x <;>
    simp [laplacian, Matrix.mulVec, dotProduct, Matrix.mul_apply, orientedIncidence_apply,
      Fin.sum_univ_two, Fin.sum_univ_three] <;> norm_num

/-- Tetali's hitting-time identity on the path: `E_0[τ_2] = 4 = 1 · 2 + 2 · 1 + 1 · 0`. -/
example : (![4, 3, 0] : Fin 3 → ℝ) 0 =
    ∑ x, weightedDegree e₁ e₂ (fun _ => 1) x * (![2, 1, 0] : Fin 3 → ℝ) x :=
  hitting_time_identity e₁ e₂ (fun _ => one_pos) (by decide) connected hit2
    laplacian_mulVec_210 rfl

/-- The first-step equations have a solution, and it is the one computed above. -/
example : ∃ h, IsHittingTimeSolution e₁ e₂ (fun _ => (1 : ℝ)) 2 h ∧ h 0 = 4 := by
  obtain ⟨h, hh⟩ := exists_isHittingTimeSolution e₁ e₂ (w := fun _ => (1 : ℝ))
    (fun _ => one_pos) (by decide) connected 2
  refine ⟨h, hh, ?_⟩
  rw [isHittingTimeSolution_unique e₁ e₂ (fun _ => one_pos) (by decide) connected hh hit2]
  rfl

/-! The loop convention. Edge `0` joins `0` and `1`, edge `1` is a loop at `0`, unit conductances.
`weightedDegree` counts the loop at both ends, so `π(0) = 3`, and the first-step equations for
`z = 1` have the solution `h(0) = 3`. The source's network walk counts the loop once (it stays at
`0` with probability `1/2`), so `E_0[τ_1] = 2`: with loops the system describes the walk with the
loop's conductance doubled, which is why the hitting-time theorems assume no loops. -/

/-- First endpoints for the loop example. -/
abbrev l₁ : Fin 2 → Fin 2 := ![0, 0]
/-- Second endpoints for the loop example. -/
abbrev l₂ : Fin 2 → Fin 2 := ![1, 0]

example : weightedDegree l₁ l₂ (fun _ => (1 : ℝ)) 0 = 3 := by
  simp [weightedDegree, Fin.sum_univ_two]; norm_num

example : IsHittingTimeSolution l₁ l₂ (fun _ => 1) 1 ![3, 0] := by
  refine ⟨rfl, fun x hx => ?_⟩
  fin_cases x
  · simp [weightedDegree, neighbourSum, Fin.sum_univ_two]; norm_num
  · exact absurd rfl hx

example : ¬ IsHittingTimeSolution l₁ l₂ (fun _ => 1) 1 ![2, 0] := by
  rintro ⟨-, h⟩
  have := h 0 (by decide)
  simp [weightedDegree, neighbourSum, Fin.sum_univ_two] at this
  norm_num at this

end EndpointMapMultigraphCommuteTimeTest
