/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Groundwater solutes and contaminant transport: retardation

## i. Overview

For saturated transport with linear sorption `S = Kd * c`, total
storage per bulk volume is `(phi + rho_b * Kd) * c`, and the
retardation factor is `R = 1 + rho_b * Kd / phi`.

Hypotheses: `phi > 0`, `rho_b ≥ 0`, `Kd ≥ 0`; instantaneous reversible
linear equilibrium sorption, constant properties. Units: `rho_b` is
dry-solid mass per bulk volume, `Kd` is volume per mass, `R` is
dimensionless. Here `c` is the aqueous dissolved concentration;
`phi * c` is its dissolved storage per bulk volume (the dissolved
storage contribution), distinguished from total storage
(`totalStorage`). For one fixed bulk cell of volume `V`, stored mass is
`V` times total storage per bulk volume; its dissolved part occupies
carrier-water volume `V * phi`. No decay or kinetic-sorption claim is made.

## ii. Key results

- `total_storage_eq`, `total_storage_eq_retardation`: total storage
  is `(phi + rho_b * Kd) * c = phi * R * c`.
- `retardation_eq_one_of_Kd_eq_zero`,
  `retardation_eq_one_of_rho_b_eq_zero`: no sorption gives `R = 1`
  for positive porosity.
- `one_le_retardationFactor`, `retardationFactor_pos`: bounds for
  admissible parameters.
- `storedMass_eq_coefficient_mul`, `storedMass_eq_retardation`,
  `concentration_eq_storedMass_div`: stored mass in one fixed bulk
  cell and its reversible concentration conversion.

## iii. Table of contents

- A. Definitions
- B. Storage identities
- C. No-sorption cases and bounds

## iv. References

- C. W. Fetter, *Contaminant Hydrogeology*, 3rd edition, Waveland Press,
  2008. The linear-equilibrium retardation factor
  `R = 1 + rho_b * Kd / phi` for a sorbing solute in saturated flow.
- R. A. Freeze and J. A. Cherry, *Groundwater*, Prentice-Hall, 1979.
  Retardation of a sorbing solute by linear equilibrium sorption.
- Field arithmetic in Mathlib (`field_simp`, `ring`).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Definitions -/

/-- Retardation factor `R = 1 + rho_b * Kd / phi` for saturated
transport with linear sorption: `phi` porosity, `rho_b` dry bulk
density, `Kd` distribution coefficient. With the convention `x / 0 = 0` it is `1` when
`phi = 0`; the intended domain is `phi > 0`, `rho_b ≥ 0`, `Kd ≥ 0`. -/
noncomputable def retardationFactor (phi rho_b Kd : ℝ) : ℝ :=
  1 + rho_b * Kd / phi

/-- Total storage per bulk volume: dissolved storage `phi * c` plus sorbed
`rho_b * (Kd * c)` (linear equilibrium sorption `S = Kd * c`, where `c` is
the aqueous dissolved concentration). -/
noncomputable def totalStorage (phi rho_b Kd c : ℝ) : ℝ :=
  phi * c + rho_b * (Kd * c)

/-- Stored solute mass in one fixed bulk cell of volume `V`:
the bulk volume times total storage per bulk volume. The cell
volume is fixed; a variable-volume update is a separate model.
The dissolved part occupies carrier-water volume `V * phi`;
the sorbed part is mass on the solids in the same bulk cell. -/
noncomputable def storedMass (V phi rho_b Kd c : ℝ) : ℝ :=
  V * totalStorage phi rho_b Kd c

/-- Scalar coefficient converting aqueous concentration to stored
mass in one fixed bulk cell: `V * (phi + rho_b * Kd)`. It is
positive under the hypotheses of `storedMassCoefficient_pos`. -/
noncomputable def storedMassCoefficient (V phi rho_b Kd : ℝ) : ℝ :=
  V * (phi + rho_b * Kd)

/-! ## B. Storage identities -/

/-- Total storage equals `(phi + rho_b * Kd) * c`. -/
theorem total_storage_eq (phi rho_b Kd c : ℝ) :
    totalStorage phi rho_b Kd c = (phi + rho_b * Kd) * c := by
  unfold totalStorage
  ring

/-- For nonzero porosity `phi`, total storage equals `phi * R * c`: the
dissolved storage `phi * c` scaled by the retardation factor. -/
theorem total_storage_eq_retardation (phi rho_b Kd c : ℝ) (hphi : phi ≠ 0) :
    totalStorage phi rho_b Kd c = phi * retardationFactor phi rho_b Kd * c := by
  unfold totalStorage retardationFactor
  field_simp

/-- Stored mass is the storage coefficient times concentration. -/
theorem storedMass_eq_coefficient_mul (V phi rho_b Kd c : ℝ) :
    storedMass V phi rho_b Kd c
      = storedMassCoefficient V phi rho_b Kd * c := by
  unfold storedMass storedMassCoefficient totalStorage
  ring

/-- Stored mass in retardation form: for nonzero porosity it is
`V * phi * R * c`, using the existing retardation factor. -/
theorem storedMass_eq_retardation (V phi rho_b Kd c : ℝ)
    (hphi : phi ≠ 0) :
    storedMass V phi rho_b Kd c
      = V * phi * retardationFactor phi rho_b Kd * c := by
  unfold storedMass totalStorage retardationFactor
  field_simp

/-- The concentration-to-stored-mass conversion is reversible
when its scalar coefficient is nonzero. A zero coefficient is
not inverted. -/
theorem concentration_eq_storedMass_div {V phi rho_b Kd c : ℝ}
    (hcoeff : storedMassCoefficient V phi rho_b Kd ≠ 0) :
    c = storedMass V phi rho_b Kd c
      / storedMassCoefficient V phi rho_b Kd := by
  rw [storedMass_eq_coefficient_mul, mul_div_cancel_left₀ _ hcoeff]

/-- With no sorption (`Kd = 0`), stored mass is just the
dissolved mass `V * phi * c`. -/
theorem storedMass_zero_sorption (V phi rho_b c : ℝ) :
    storedMass V phi rho_b 0 c = V * phi * c := by
  unfold storedMass totalStorage
  ring

/-! ## C. No-sorption cases and bounds -/

/-- No sorption (`Kd = 0`) gives `R = 1` for positive porosity. -/
theorem retardation_eq_one_of_Kd_eq_zero (phi rho_b : ℝ) (hphi : 0 < phi) :
    retardationFactor phi rho_b 0 = 1 := by
  have hne : phi ≠ 0 := ne_of_gt hphi
  unfold retardationFactor
  field_simp
  ring

/-- No solid mass (`rho_b = 0`) gives `R = 1` for positive porosity. -/
theorem retardation_eq_one_of_rho_b_eq_zero (phi Kd : ℝ) (hphi : 0 < phi) :
    retardationFactor phi 0 Kd = 1 := by
  have hne : phi ≠ 0 := ne_of_gt hphi
  unfold retardationFactor
  field_simp
  ring

/-- Retardation is at least `1` for admissible parameters `phi > 0`,
`rho_b ≥ 0` and `Kd ≥ 0`. -/
theorem one_le_retardationFactor {phi rho_b Kd : ℝ} (hphi : 0 < phi)
    (hrho : 0 ≤ rho_b) (hKd : 0 ≤ Kd) :
    1 ≤ retardationFactor phi rho_b Kd := by
  unfold retardationFactor
  have h : 0 ≤ rho_b * Kd / phi := div_nonneg (mul_nonneg hrho hKd) (le_of_lt hphi)
  exact le_add_of_nonneg_right h

/-- Retardation is positive for admissible parameters `phi > 0`,
`rho_b ≥ 0` and `Kd ≥ 0`. -/
theorem retardationFactor_pos {phi rho_b Kd : ℝ} (hphi : 0 < phi)
    (hrho : 0 ≤ rho_b) (hKd : 0 ≤ Kd) :
    0 < retardationFactor phi rho_b Kd := by
  exact lt_of_lt_of_le zero_lt_one (one_le_retardationFactor hphi hrho hKd)

/-- The storage coefficient is positive for a positive cell
volume, positive porosity, and nonnegative linear-sorption data. -/
theorem storedMassCoefficient_pos {V phi rho_b Kd : ℝ}
    (hV : 0 < V) (hphi : 0 < phi) (hrho : 0 ≤ rho_b)
    (hKd : 0 ≤ Kd) :
    0 < storedMassCoefficient V phi rho_b Kd := by
  unfold storedMassCoefficient
  positivity

/-- Nonnegative concentration gives nonnegative stored mass for
positive volume and porosity and nonnegative sorption data. -/
theorem storedMass_nonneg {V phi rho_b Kd c : ℝ}
    (hV : 0 < V) (hphi : 0 < phi) (hrho : 0 ≤ rho_b)
    (hKd : 0 ≤ Kd) (hc : 0 ≤ c) :
    0 ≤ storedMass V phi rho_b Kd c := by
  rw [storedMass_eq_coefficient_mul]
  exact mul_nonneg
    (le_of_lt (storedMassCoefficient_pos hV hphi hrho hKd)) hc

end EarthScience
