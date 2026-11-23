/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.FluidDynamics.ShearReduction
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Parallel shear flow checks

Concrete consumers of `PhyslibExt.FluidDynamics.ShearReduction`: the single-mode transient
with unit density, viscosity, wall speed and gap.

## i. Overview

These are elaboration and non-vacuity checks, not new results. At `ρ = μ = A = L = 1` and
`t = 0` the single-mode flow is a Navier-Stokes solution, its wall shear stress is `2`, its
kinetic energy is positive and grows, and the energy balance is wall work `2` minus dissipation
`3/2`; the balance without the wall term would give `-3/2`. Its initial value at `y = 1/2` is
`1/2 - 1/π ≠ 0` and its moving wall already has velocity `1`, so it does not start from rest.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. The single-mode flow at unit parameters

## iv. References

- `PhyslibExt.FluidDynamics.ShearReduction`
-/

open ShearReduction FluidDynamics

/-! ## A. The single-mode flow at unit parameters -/

/-- The single-mode flow with `ρ = μ = A = L = 1`, any uniform pressure and zero second viscosity is
a Navier-Stokes solution. -/
example (p : Time → ℝ) :
    NavierStokes 3 (shearFlow 1 1 0 p (singleModeProfile 1 1 (1 / 1))) (fun t _ => p t)
      (fun _ _ => 1) (fun _ _ => 0) :=
  singleModeFlow_navierStokes one_pos 1 1 1 0 p

/-- Energy balance at `t = 0`: dissipation `3/2`, wall work `2` and kinetic-energy derivative
`1/2`. -/
example :
    1 * (∫ y in (0 : ℝ)..1, deriv (singleModeProfile 1 1 (1 / 1) 0) y ^ 2) = 3 / 2 ∧
      1 * deriv (singleModeProfile 1 1 (1 / 1) 0) 1 * 1 = 2 ∧
      HasDerivAt (shearKineticEnergy 1 1 (singleModeProfile 1 1 (1 / 1))) (1 / 2) 0 := by
  obtain ⟨h1, h2, h3⟩ := singleModeProfile_energy_balance (ρ := 1) (L := 1) one_pos one_pos 1 1 0
  refine ⟨?_, ?_, h3.congr_deriv ?_⟩
  · rw [h1]
    norm_num
  · rw [h2]
    norm_num
  · norm_num

/-- The wall shear stress of the single-mode flow on the moving wall `y = 1` at `t = 0` is `2`. -/
example (x : Space) (hx : x 1 = 1) :
    (shearFlow 1 1 0 (fun _ => 0) (singleModeProfile 1 1 (1 / 1))).stress ⟨0⟩ x 0 1 = 2 := by
  have h2 := (singleModeProfile_energy_balance (ρ := 1) (L := 1) one_pos one_pos 1 1 0).2.1
  rw [shearFlow_stress (singleModeProfile_contDiff 1 1 (1 / 1))]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, hx]
  norm_num at h2 ⊢
  exact h2

/-- Positive and increasing kinetic energy, and the failure of the balance without wall work, at
unit parameters. -/
example :
    0 < shearKineticEnergy 1 1 (singleModeProfile 1 1 (1 / 1)) 0 ∧
      shearKineticEnergy 1 1 (singleModeProfile 1 1 (1 / 1)) 0 <
        shearKineticEnergy 1 1 (singleModeProfile 1 1 (1 / 1)) 1 ∧
      ¬ HasDerivAt (shearKineticEnergy 1 1 (singleModeProfile 1 1 (1 / 1)))
        (-1 * ∫ y in (0 : ℝ)..1, deriv (singleModeProfile 1 1 (1 / 1) 0) y ^ 2) 0 :=
  ⟨singleModeProfile_energy_pos one_pos one_pos one_pos one_ne_zero le_rfl,
    singleModeProfile_energy_strictMonoOn one_pos one_pos one_pos one_ne_zero
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one) zero_lt_one,
    singleModeProfile_no_wall_work one_pos one_pos one_pos one_ne_zero le_rfl⟩

/-- Not a start from rest: at `t = 0` the single-mode profile with `A = L = 1` has the interior
value `1/2 - 1/π ≠ 0` at `y = 1/2`, and its wall `y = 1` already moves with velocity `1`. -/
example (ν : ℝ) :
    singleModeProfile 1 1 ν 0 (1 / 2) = 1 / 2 - 1 / Real.pi ∧
      singleModeProfile 1 1 ν 0 (1 / 2) ≠ 0 ∧ singleModeProfile 1 1 ν 0 1 = 1 := by
  have h : singleModeProfile 1 1 ν 0 (1 / 2) = 1 / 2 - 1 / Real.pi := by
    simp only [singleModeProfile]
    rw [show Real.pi * (1 / 2) / 1 = Real.pi / 2 by ring, Real.sin_pi_div_two]
    simp
  have hπ := Real.pi_gt_three
  have hlt : 1 / Real.pi < 1 / 2 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  refine ⟨h, ?_, (singleModeProfile_walls one_ne_zero 1 ν 0).2⟩
  rw [h]
  linarith

/-- The steady member of the shear family is the plane Couette velocity. -/
example (t : Time) :
    shearVelocity (fun _ y => 2 * y / 1) t = FlowCoordinateBernoulli.couetteVelocity 2 1 :=
  shearVelocity_couette 2 1 t
