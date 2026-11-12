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
`R ≥ 1` for admissible parameters.
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

#print axioms retardationFactor
#print axioms totalStorage
#print axioms total_storage_eq_retardation

end EarthScience
