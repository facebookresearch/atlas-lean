/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.ThomsonPrinciple

@[expose] public section

namespace EndpointMapMultigraphThomsonPrincipleTest

open EndpointMapMultigraph Matrix

/-- The path `0 - 1 - 2` with unit conductances. -/
abbrev e₁ : Fin 2 → Fin 3 := ![0, 1]
/-- Second endpoints of the path `0 - 1 - 2`. -/
abbrev e₂ : Fin 2 → Fin 3 := ![1, 2]

theorem loopless : ∀ e, e₁ e ≠ e₂ e := by decide

theorem reach02 : (underlyingGraph e₁ e₂).Reachable 0 2 :=
  ((underlyingGraph_adj_of_ne e₁ e₂ (e := 0) (by decide)).reachable).trans
    ((underlyingGraph_adj_of_ne e₁ e₂ (e := 1) (by decide)).reachable)

/-- Sending one unit along both edges is a unit flow from `0` to `2`. -/
theorem isUnitFlow_one : IsUnitFlow e₁ e₂ 0 2 (fun _ => 1) := by
  rw [IsUnitFlow]
  funext x
  fin_cases x <;>
    simp only [Matrix.mulVec, dotProduct, orientedIncidence_apply, Fin.sum_univ_two] <;>
    norm_num [Pi.single_apply]

/-- The potential `(2, 1, 0)` solves `L v = δ₀ - δ₂`, so `R_eff(0, 2) = 2` (two unit resistors in
series). -/
theorem laplacian_mulVec_210 :
    laplacian e₁ e₂ (fun _ => 1) *ᵥ ![2, 1, 0] = Pi.single 0 1 - Pi.single 2 1 := by
  funext x
  fin_cases x <;>
    simp [laplacian, Matrix.mulVec, dotProduct, Matrix.mul_apply, orientedIncidence_apply,
      Fin.sum_univ_two, Fin.sum_univ_three] <;> norm_num

theorem effectiveResistance_02 : effectiveResistance e₁ e₂ (fun _ => 1) 0 2 = 2 := by
  have h := (effectiveResistance_eq_sub_of_laplacian_mulVec e₁ e₂ (fun _ => zero_le_one)
    (by decide) laplacian_mulVec_210).1
  rw [h]
  norm_num

/-- Thomson's principle on the path: the unit flow `1` has energy `2 = R_eff(0, 2)`, so it is the
unit current (non-degenerate instance of `effectiveResistance_le_flowEnergy`). -/
example : effectiveResistance e₁ e₂ (fun _ => 1) 0 2 ≤
    flowEnergy (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 1) :=
  effectiveResistance_le_flowEnergy e₁ e₂ (fun _ => one_pos) loopless (by decide) isUnitFlow_one

example : flowEnergy (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 1) = 2 := by
  norm_num [flowEnergy]

/-- The equality case identifies the unit flow `1` with the current of `(2, 1, 0)`. -/
example : (fun _ : Fin 2 => (1 : ℝ)) = currentOf e₁ e₂ (fun _ => 1) ![2, 1, 0] := by
  refine (flowEnergy_eq_effectiveResistance_iff e₁ e₂ (fun _ => one_pos) (by decide)
    laplacian_mulVec_210 isUnitFlow_one).1 ?_
  rw [effectiveResistance_02]
  norm_num [flowEnergy]

/-- `R_eff(0, 2)` is the least energy of a unit flow. -/
example : IsLeast {q | ∃ θ, IsUnitFlow e₁ e₂ 0 2 θ ∧ q = flowEnergy (fun _ => 1) θ} 2 := by
  have h := isLeast_flowEnergy e₁ e₂ (w := fun _ => 1) (fun _ => one_pos) loopless (by decide)
    reach02
  rwa [effectiveResistance_02] at h

/-- Dirichlet's principle on the path: `C_eff(0, 2) = 1 / 2` is the least energy of a potential
that is `0` at `0` and `1` at `2`. -/
example : IsLeast {q | ∃ x : Fin 3 → ℝ, x 0 = 0 ∧ x 2 = 1 ∧
    q = x ⬝ᵥ (laplacian e₁ e₂ (fun _ => 1) *ᵥ x)} (1 / 2) := by
  have h := isLeast_dirichletEnergy e₁ e₂ (w := fun _ => 1) (fun _ => one_pos) loopless
    (by decide) reach02
  have hC : effectiveConductance e₁ e₂ (fun _ => 1) 0 2 = 1 / 2 := by
    have := effectiveResistance_02
    rw [effectiveResistance] at this
    rw [← inv_inv (effectiveConductance e₁ e₂ (fun _ => 1) 0 2), this]
    norm_num
  rwa [hC] at h

/-! Non-uniform instances: two parallel unit edges, and one edge of conductance `3`. -/

/-- Two parallel edges between `0` and `1`. -/
abbrev p₁ : Fin 2 → Fin 2 := ![0, 0]
/-- Second endpoints of the two parallel edges. -/
abbrev p₂ : Fin 2 → Fin 2 := ![1, 1]

/-- Parallel unit resistors: `R_eff(0, 1) = 1 / 2`. -/
example : effectiveResistance p₁ p₂ (fun _ => 1) 0 1 = 1 / 2 := by
  have hv : laplacian p₁ p₂ (fun _ => 1) *ᵥ ![1 / 2, 0] = Pi.single 0 1 - Pi.single 1 1 := by
    funext x
    fin_cases x <;>
      simp [laplacian, Matrix.mulVec, dotProduct, Matrix.mul_apply, orientedIncidence_apply,
        Fin.sum_univ_two] <;> norm_num
  have h := (effectiveResistance_eq_sub_of_laplacian_mulVec p₁ p₂ (fun _ => zero_le_one)
    (by decide) hv).1
  rw [h]
  norm_num

/-- Splitting the unit flow evenly over the parallel edges attains `R_eff = 1 / 2`; sending it all
along one edge costs `1`. -/
example : flowEnergy (fun _ : Fin 2 => (1 : ℝ)) ![1 / 2, 1 / 2] = 1 / 2 ∧
    flowEnergy (fun _ : Fin 2 => (1 : ℝ)) ![1, 0] = 1 := by
  constructor <;> norm_num [flowEnergy, Fin.sum_univ_two]

/-- A single edge of conductance `3`: `R_eff(0, 1) = 1 / 3`, so `w` enters as a conductance. -/
example : effectiveResistance (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3) 0 1 =
    1 / 3 := by
  have hv : laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3) *ᵥ ![1 / 3, 0] =
      Pi.single 0 1 - Pi.single 1 1 := by
    funext x
    fin_cases x <;>
      simp [laplacian, Matrix.mulVec, dotProduct, Matrix.mul_apply, orientedIncidence_apply]
  have h := (effectiveResistance_eq_sub_of_laplacian_mulVec (fun _ : Unit => (0 : Fin 2))
    (fun _ => 1) (fun _ => by norm_num) (by decide) hv).1
  rw [h]
  norm_num

end EndpointMapMultigraphThomsonPrincipleTest
