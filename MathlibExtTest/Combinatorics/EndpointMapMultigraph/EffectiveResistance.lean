/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.EffectiveResistance

@[expose] public section

namespace EndpointMapMultigraphEffectiveResistanceTest

open EndpointMapMultigraph Matrix

/-- Across one edge of conductance `3`, the potential `(0, 1)` shows `C_eff(0, 1) ≤ 3`. -/
example :
    effectiveConductance (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3) 0 1 ≤ 3 := by
  have h := effectiveConductance_le_energy (fun _ : Unit => (0 : Fin 2)) (fun _ => 1)
    (w := fun _ => (3 : ℝ)) (fun _ => by norm_num) (s := 0) (t := 1) (x := ![0, 1]) rfl rfl
  rw [dotProduct_mulVec_laplacian] at h
  simpa using h

/-- Rayleigh monotonicity: halving the conductance cannot raise `C_eff`. -/
example : effectiveConductance (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 1) 0 1 ≤
    effectiveConductance (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 2) 0 1 :=
  effectiveConductance_mono _ _ (fun _ => by norm_num) (fun _ => by norm_num) 0 1

/-- Effective conductance is nonnegative. -/
example : 0 ≤ effectiveConductance (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 1) 0 1 :=
  effectiveConductance_nonneg _ _ (fun _ => by norm_num) 0 1

/-- One edge of conductance `3` between the two vertices of `Fin 2`. -/
theorem edge_connected :
    (underlyingGraph (fun _ : Unit => (0 : Fin 2)) (fun _ => 1)).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, ⟨0⟩⟩
  have h01 : (underlyingGraph (fun _ : Unit => (0 : Fin 2)) (fun _ => 1)).Reachable 0 1 :=
    (underlyingGraph_adj_of_ne (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (e := ())
      (by decide)).reachable
  fin_cases u <;> fin_cases v
  · rfl
  · exact h01
  · exact h01.symm
  · rfl

/-- The potentials `(1/3, 0)` carry one unit of current across the edge. -/
theorem edge_potential :
    laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => (3 : ℝ)) *ᵥ ![1 / 3, 0] =
      Pi.single 0 1 - Pi.single 1 1 := by
  funext u
  fin_cases u <;>
    simp [laplacian, orientedIncidence, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Matrix.diagonal, Fin.sum_univ_two, -Matrix.transpose_of]

/-- Hence the effective resistance across the edge is `1/3`, the reciprocal conductance. -/
example :
    effectiveResistance (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3) 0 1 = 1 / 3 := by
  have h := (effectiveResistance_eq_sub_of_laplacian_mulVec (fun _ : Unit => (0 : Fin 2))
    (fun _ => 1) (w := fun _ => (3 : ℝ)) (fun _ => by norm_num) (s := 0) (t := 1) (by decide)
    edge_potential).1
  simpa using h

/-- Foster's identity on the edge: `w R_eff = n - 1 = 1`. -/
example : ∑ e, (fun _ : Unit => (3 : ℝ)) e *
    effectiveResistance (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3)
      ((fun _ : Unit => (0 : Fin 2)) e) ((fun _ : Unit => (1 : Fin 2)) e) = 1 := by
  rw [sum_mul_effectiveResistance _ _ (fun _ => by norm_num) (fun _ => by decide) edge_connected]
  norm_num

end EndpointMapMultigraphEffectiveResistanceTest
