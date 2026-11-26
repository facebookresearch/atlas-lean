/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.PerUnitBases
import Mathlib.Tactic.NormNum

@[expose] public section

open ComplexConjugate
open PhyslibExt.Circuits.PerUnitBases
open PhyslibExt.Circuits.BalancedThreePhase

namespace PhyslibExtTest.Circuits.PerUnitBases

/-- At bases `Vb = 2` and `Ib = 4`, the three-phase power base
is `24`. -/
example : threePhasePowerBase 2 4 = 24 := by
  norm_num [threePhasePowerBase]

/-- At bases `Vb = 2` and `Ib = 4`, the impedance base is `1 / 2`. -/
example : impedanceBase 2 4 = 1 / 2 := by
  norm_num [impedanceBase]

/-- At bases `Vb = 2` and `Ib = 4`, all three bases are
positive. -/
example : 0 < threePhasePowerBase 2 4 ∧ 0 < impedanceBase 2 4 ∧
    0 < lineVoltageBase 2 :=
  bases_pos 2 4 (by norm_num) (by norm_num)

/-- The line-base identity at `Vb = 2` and `Ib = 4`:
`(sqrt 3 * 2) ^ 2 / 24 = 1 / 2`. -/
example : lineVoltageBase 2 ^ 2 / threePhasePowerBase 2 4 = 1 / 2 := by
  rw [← impedanceBase_eq_lineVoltageBase_sq_div 2 4 (by norm_num) (by norm_num)]
  norm_num [impedanceBase]

/-- Multiplying a per-unit voltage by its base recovers the physical
voltage, at base `Vb = 2`. -/
example (V : ℂ) : (2 : ℂ) * voltagePerUnit 2 V = V :=
  base_mul_voltagePerUnit 2 (by norm_num) V

/-- A concrete per-unit Ohm check: with `V = 6`, `Z = 3` and
`I = 2` at bases `Vb = 2` and `Ib = 4`, the per-unit quantities
satisfy `Vpu = Zpu * Ipu`, namely `3 = 6 * (1 / 2)`. -/
example : voltagePerUnit 2 (6 : ℂ) =
    impedancePerUnit 2 4 (3 : ℂ) * currentPerUnit 4 (2 : ℂ) :=
  (ohm_perUnit_iff 2 4 (by norm_num) (by norm_num) 6 3 2).mp (by norm_num)

/-- The balanced power identity at bases `Vb = 2` and `Ib = 4`,
read through the summed phase powers. -/
example (V I : ℂ) : powerPerUnit 2 4
    (∑ p, complexPower (balancedPhases V p) (balancedPhases I p)) =
    voltagePerUnit 2 V * conj (currentPerUnit 4 I) :=
  balancedPower_perUnit 2 4 (by norm_num) (by norm_num) V I

/-- The line-voltage base at `Vb = 2` is the magnitude of the
balanced line voltage built from the phase base. -/
example (p : ZMod 3) : lineVoltageBase 2 =
    ‖lineVoltage (balancedPhases (2 : ℂ)) p‖ :=
  lineVoltageBase_eq_norm_lineVoltage 2 (by norm_num) p

/-- Using the squared phase-voltage base at `Vb = 2` and `Ib = 4`
gives one third of the impedance base. -/
example : (2 : ℝ) ^ 2 / threePhasePowerBase 2 4 = impedanceBase 2 4 / 3 :=
  phaseVoltageBase_sq_div_powerBase 2 4 (by norm_num) (by norm_num)

end PhyslibExtTest.Circuits.PerUnitBases
