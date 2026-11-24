/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.GroundwaterRetardation
import Mathlib.Tactic.NormNum

/-!
# Tests for groundwater retardation

Closed checks: the witness `phi = 0.3, rho_b = 1.5, Kd = 0.2, c = 2`
gives `R = 2` and total storage `1.2`, no sorption gives `R = 1`, and
`R ≥ 1` for admissible parameters. With bulk-cell volume `V = 5`, the
same witness has stored-mass coefficient `3`, stored mass `6`, and
inverse concentration `2`; zero-sorption, zero-volume, and
zero-coefficient controls are included.
-/

namespace EarthScience

/-- Witness: `phi = 3/10, rho_b = 3/2, Kd = 1/5` gives `R = 2`. -/
example : retardationFactor (3 / 10) (3 / 2) (1 / 5) = 2 := by
  norm_num [retardationFactor]

/-- Witness: total storage at `c = 2` is `6/5 = phi * R * c`. -/
example : totalStorage (3 / 10) (3 / 2) (1 / 5) 2 = 6 / 5 := by
  norm_num [totalStorage]

/-- No sorption: `Kd = 0` gives `R = 1` for positive porosity. -/
example (phi rho_b : ℝ) (hphi : 0 < phi) : retardationFactor phi rho_b 0 = 1 :=
  retardation_eq_one_of_Kd_eq_zero phi rho_b hphi

/-- No solid mass: `rho_b = 0` gives `R = 1` for positive porosity. -/
example (phi Kd : ℝ) (hphi : 0 < phi) : retardationFactor phi 0 Kd = 1 :=
  retardation_eq_one_of_rho_b_eq_zero phi Kd hphi

/-- Retardation is at least `1` for admissible parameters. -/
example {phi rho_b Kd : ℝ} (hphi : 0 < phi) (hrho : 0 ≤ rho_b) (hKd : 0 ≤ Kd) :
    1 ≤ retardationFactor phi rho_b Kd :=
  one_le_retardationFactor hphi hrho hKd

/-- Stored-mass coefficient at the witness with `V = 5` is `3`. -/
example : storedMassCoefficient 5 (3 / 10) (3 / 2) (1 / 5) = 3 := by
  norm_num [storedMassCoefficient]

/-- Stored mass at the witness with `V = 5`, `c = 2` is `6`, by direct
unfolding and by the coefficient and retardation forms. -/
example : storedMass 5 (3 / 10) (3 / 2) (1 / 5) 2 = 6 := by
  norm_num [storedMass, totalStorage]

example : storedMass 5 (3 / 10) (3 / 2) (1 / 5) 2
    = storedMassCoefficient 5 (3 / 10) (3 / 2) (1 / 5) * 2 :=
  storedMass_eq_coefficient_mul _ _ _ _ _

example : storedMass 5 (3 / 10) (3 / 2) (1 / 5) 2
    = 5 * (3 / 10) * retardationFactor (3 / 10) (3 / 2) (1 / 5) * 2 :=
  storedMass_eq_retardation _ _ _ _ _ (by norm_num)

/-- The conversion inverts at the witness. -/
example : (2 : ℝ) = storedMass 5 (3 / 10) (3 / 2) (1 / 5) 2
    / storedMassCoefficient 5 (3 / 10) (3 / 2) (1 / 5) :=
  concentration_eq_storedMass_div (by norm_num [storedMassCoefficient])

/-- Positive coefficient and nonnegative stored mass at admissible data. -/
example : 0 < storedMassCoefficient 5 (3 / 10) (3 / 2) (1 / 5) :=
  storedMassCoefficient_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

example : 0 ≤ storedMass 5 (3 / 10) (3 / 2) (1 / 5) 2 :=
  storedMass_nonneg (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Zero sorption leaves dissolved mass `V * phi * c = 3`. -/
example : storedMass 5 (3 / 10) (3 / 2) 0 2 = 3 := by
  rw [storedMass_zero_sorption]
  norm_num

/-- Zero-volume and zero-coefficient controls: no stored mass and no
inverse is claimed. -/
example : storedMassCoefficient 0 (3 / 10) (3 / 2) (1 / 5) = 0 := by
  norm_num [storedMassCoefficient]

example : storedMass 0 (3 / 10) (3 / 2) (1 / 5) 2 = 0 := by
  norm_num [storedMass, totalStorage]

#print axioms retardationFactor
#print axioms totalStorage
#print axioms total_storage_eq_retardation
#print axioms storedMass_eq_coefficient_mul
#print axioms storedMass_eq_retardation
#print axioms storedMassCoefficient_pos
#print axioms concentration_eq_storedMass_div
#print axioms storedMass_zero_sorption
#print axioms storedMass_nonneg

end EarthScience
