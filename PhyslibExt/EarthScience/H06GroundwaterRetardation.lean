/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Groundwater solutes and contaminant transport: retardation (H06)

For saturated transport with linear sorption `S = Kd * c`, total
storage per bulk volume is `(phi + rho_b * Kd) * c`, and the
retardation factor is `R = 1 + rho_b * Kd / phi`.

Hypotheses: `phi > 0`, `rho_b ≥ 0`, `Kd ≥ 0`; instantaneous reversible
linear equilibrium sorption, constant properties. Units: `rho_b` is
dry-solid mass per bulk volume, `Kd` is volume per mass, `R` is
dimensionless. Dissolved concentration (`phi * c`) and total
concentration (`totalStorage`) are distinguished. No decay or
kinetic-sorption claim is made.

## Key results

- `total_storage_eq`, `total_storage_eq_retardation`: total storage
  is `(phi + rho_b * Kd) * c = phi * R * c`.
- `retardation_eq_one_of_Kd_eq_zero`,
  `retardation_eq_one_of_rho_b_eq_zero`: no sorption gives `R = 1`.
- `one_le_retardationFactor`, `retardationFactor_pos`: bounds for
  admissible parameters.
-/

@[expose] public section

namespace EarthScience

/-- Retardation factor `R = 1 + rho_b * Kd / phi` for saturated
transport with linear sorption: `phi` porosity, `rho_b` dry bulk
density, `Kd` distribution coefficient. -/
noncomputable def retardationFactor (phi rho_b Kd : ℝ) : ℝ :=
  1 + rho_b * Kd / phi

/-- Total storage per bulk volume: dissolved `phi * c` plus sorbed
`rho_b * (Kd * c)` (linear equilibrium sorption `S = Kd * c`). -/
noncomputable def totalStorage (phi rho_b Kd c : ℝ) : ℝ :=
  phi * c + rho_b * (Kd * c)

/-- Total storage equals `(phi + rho_b * Kd) * c`. -/
theorem total_storage_eq (phi rho_b Kd c : ℝ) :
    totalStorage phi rho_b Kd c = (phi + rho_b * Kd) * c := by
  unfold totalStorage
  ring

/-- Total storage equals `phi * R * c`: the dissolved concentration
times porosity times the retardation factor. -/
theorem total_storage_eq_retardation (phi rho_b Kd c : ℝ) (hphi : phi ≠ 0) :
    totalStorage phi rho_b Kd c = phi * retardationFactor phi rho_b Kd * c := by
  unfold totalStorage retardationFactor
  field_simp

/-- No sorption (`Kd = 0`) gives `R = 1`. -/
theorem retardation_eq_one_of_Kd_eq_zero (phi rho_b : ℝ) :
    retardationFactor phi rho_b 0 = 1 := by
  simp [retardationFactor]

/-- No solid mass (`rho_b = 0`) gives `R = 1`. -/
theorem retardation_eq_one_of_rho_b_eq_zero (phi Kd : ℝ) :
    retardationFactor phi 0 Kd = 1 := by
  simp [retardationFactor]

/-- Retardation is at least `1` for admissible parameters. -/
theorem one_le_retardationFactor {phi rho_b Kd : ℝ} (hphi : 0 < phi)
    (hrho : 0 ≤ rho_b) (hKd : 0 ≤ Kd) :
    1 ≤ retardationFactor phi rho_b Kd := by
  unfold retardationFactor
  have h : 0 ≤ rho_b * Kd / phi := div_nonneg (mul_nonneg hrho hKd) (le_of_lt hphi)
  exact le_add_of_nonneg_right h

/-- Retardation is positive for admissible parameters. -/
theorem retardationFactor_pos {phi rho_b Kd : ℝ} (hphi : 0 < phi)
    (hrho : 0 ≤ rho_b) (hKd : 0 ≤ Kd) :
    0 < retardationFactor phi rho_b Kd := by
  exact lt_of_lt_of_le zero_lt_one (one_le_retardationFactor hphi hrho hKd)

end EarthScience
