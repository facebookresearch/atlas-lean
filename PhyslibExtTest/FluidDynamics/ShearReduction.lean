/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.FluidDynamics.ShearReduction
import Mathlib.Tactic.NormNum

/-!
# Parallel shear flow checks

Concrete consumers of `PhyslibExt.FluidDynamics.ShearReduction`: the moving-wall startup flow
with unit density, viscosity, wall speed and gap.

## i. Overview

These are elaboration and non-vacuity checks, not new results. At `ρ = μ = A = L = 1` and
`t = 0` the startup flow is a Navier-Stokes solution, its wall shear stress is `2`, its kinetic
energy is positive and grows, and the energy balance is wall work `2` minus dissipation `3/2`;
the balance without the wall term would give `-3/2`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. The startup flow at unit parameters

## iv. References

- `PhyslibExt.FluidDynamics.ShearReduction`
-/

open ShearReduction FluidDynamics

/-! ## A. The startup flow at unit parameters -/

/-- The startup flow with `ρ = μ = A = L = 1`, any uniform pressure and zero second viscosity is
a Navier-Stokes solution. -/
example (p : Time → ℝ) :
    NavierStokes 3 (shearFlow 1 1 0 p (startupProfile 1 1 (1 / 1))) (fun t _ => p t)
      (fun _ _ => 1) (fun _ _ => 0) :=
  startupFlow_navierStokes one_pos 1 1 1 0 p

/-- Energy balance at `t = 0`: dissipation `3/2`, wall work `2` and kinetic-energy derivative
`1/2`. -/
example :
    1 * (∫ y in (0 : ℝ)..1, deriv (startupProfile 1 1 (1 / 1) 0) y ^ 2) = 3 / 2 ∧
      1 * deriv (startupProfile 1 1 (1 / 1) 0) 1 * 1 = 2 ∧
      HasDerivAt (shearKineticEnergy 1 1 (startupProfile 1 1 (1 / 1))) (1 / 2) 0 := by
  obtain ⟨h1, h2, h3⟩ := startupProfile_energy_balance (ρ := 1) (L := 1) one_pos one_pos 1 1 0
  refine ⟨?_, ?_, h3.congr_deriv ?_⟩
  · rw [h1]
    norm_num
  · rw [h2]
    norm_num
  · norm_num

/-- The wall shear stress of the startup flow on the moving wall `y = 1` at `t = 0` is `2`. -/
example (x : Space) (hx : x 1 = 1) :
    (shearFlow 1 1 0 (fun _ => 0) (startupProfile 1 1 (1 / 1))).stress ⟨0⟩ x 0 1 = 2 := by
  have h2 := (startupProfile_energy_balance (ρ := 1) (L := 1) one_pos one_pos 1 1 0).2.1
  rw [shearFlow_stress (startupProfile_contDiff 1 1 (1 / 1))]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, hx]
  norm_num at h2 ⊢
  exact h2

/-- Positive and increasing kinetic energy, and the failure of the balance without wall work, at
unit parameters. -/
example :
    0 < shearKineticEnergy 1 1 (startupProfile 1 1 (1 / 1)) 0 ∧
      shearKineticEnergy 1 1 (startupProfile 1 1 (1 / 1)) 0 <
        shearKineticEnergy 1 1 (startupProfile 1 1 (1 / 1)) 1 ∧
      ¬ HasDerivAt (shearKineticEnergy 1 1 (startupProfile 1 1 (1 / 1)))
        (-1 * ∫ y in (0 : ℝ)..1, deriv (startupProfile 1 1 (1 / 1) 0) y ^ 2) 0 :=
  ⟨startupProfile_energy_pos one_pos one_pos one_pos one_ne_zero le_rfl,
    startupProfile_energy_strictMonoOn one_pos one_pos one_pos one_ne_zero (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr zero_le_one) zero_lt_one,
    startupProfile_no_wall_work one_pos one_pos one_pos one_ne_zero le_rfl⟩

/-- The steady member of the shear family is the plane Couette velocity. -/
example (t : Time) :
    shearVelocity (fun _ y => 2 * y / 1) t = FlowCoordinateBernoulli.couetteVelocity 2 1 :=
  shearVelocity_couette 2 1 t
