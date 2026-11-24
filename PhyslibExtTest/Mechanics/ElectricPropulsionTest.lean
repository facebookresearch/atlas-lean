/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.ElectricPropulsion
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Mechanics.ElectricPropulsion`

* An ion of mass `2` and charge `1` accelerated through `9` leaves at `v_e = 3`; the current `2`
  carries `ṁ = 4` and the beam power `18`, and with `γ_div = 9/10` and `P_in = 20` the thrust is
  `54/5` and the thrust efficiency `729/1000`.
* The same beam: `2` ions per unit time of charge `1` carry the current `2`; each ion leaves with
  the kinetic energy `9` and the beam carries the kinetic power `18`; as a pressure-matched rocket
  its effective exhaust velocity is `27/10` and its specific impulse `(27/10) / g0`; the efficiency
  is `(18/20) (9/10)² ≤ 1`.
* A uniform accelerating gap: under the potential `-9 x` an ion of mass `2` and charge `1` released
  at rest follows the constant-force trajectory of `PowerPorts`, crosses the gap `[0, 1]` at
  `t = 2/3` and leaves at the speed `√(2 · 1 · 9 / 2)` given by the work-energy lemma.
* Xenon ions with the exact SI elementary charge and Avogadro constant: the molar flow is
  `I_b / F`, and the molar mass in place of the ion mass multiplies the mass flow by `N_A`.
* Zero beam current gives zero mass flow and a zero efficiency denominator, while each ion would
  still leave at a positive speed.
-/

@[expose] public section

namespace PhyslibExtTest.Mechanics.ElectricPropulsion

open _root_.PhyslibExt.Mechanics _root_.PhyslibExt.Mechanics.PropulsionPorts
  _root_.PhyslibExt.Mechanics.ElectricPropulsion

/-- **A nonzero beam with a divergence factor below one.** An ion of mass `2` and charge `1`
accelerated through `9` leaves at `v_e = 3`; the current `2` carries `ṁ = 4` and the beam power
`18`. With `γ_div = 9/10` the thrust is `54/5`, and at `P_in = 20` the thrust efficiency is
`729/1000 = (18/20) (9/10)²`. -/
lemma ion_fixture :
    ionExhaustSpeed 2 1 9 = 3 ∧ beamMassFlow 2 1 2 = 4 ∧ beamPower 9 2 = 18 ∧
      ionThrust 2 1 9 2 (9 / 10) = 54 / 5 ∧
      thrustEfficiency (ionThrust 2 1 9 2 (9 / 10)) (beamMassFlow 2 1 2) 20 = 729 / 1000 := by
  have hv : ionExhaustSpeed 2 1 9 = 3 := by
    rw [ionExhaustSpeed, show (2 : ℝ) * 1 * 9 / 2 = 3 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hT : ionThrust 2 1 9 2 (9 / 10) = 54 / 5 := by
    rw [ionThrust, hv, beamMassFlow]
    norm_num
  refine ⟨hv, by norm_num [beamMassFlow], by norm_num [beamPower], hT, ?_⟩
  rw [hT, thrustEfficiency, beamMassFlow]
  norm_num

/-- **A uniform accelerating gap.** On the line the potential `φ x = -9 x` has the uniform field
`9`. An ion of mass `2` and charge `1` released at rest at `0` feels the constant force `9` and
follows the constant-force trajectory of `PowerPorts`; at `t = 2/3` it has crossed the gap
`[0, 1]`, falling through `V_b = 9`, and its speed is `v_e = √(2 · 1 · 9 / 2)`. -/
lemma uniformGap_fixture :
    PowerPorts.constForcePosition 2 (0 : ℝ) 0 9 (2 / 3) = 1 ∧
      ‖PowerPorts.constForceVelocity 2 (0 : ℝ) 9 (2 / 3)‖ = ionExhaustSpeed 2 1 9 := by
  have hpos : PowerPorts.constForcePosition 2 (0 : ℝ) 0 9 (2 / 3) = 1 := by
    rw [PowerPorts.constForcePosition]
    norm_num
  refine ⟨hpos, ?_⟩
  have hφ : ∀ x : ℝ, HasFDerivAt (fun y : ℝ => -9 * y) (innerSL ℝ (-9 : ℝ)) x := fun x =>
    ((hasDerivAt_id x).const_mul (-9)).hasFDerivAt.congr_fderiv (by ext; simp)
  refine (ion_exitSpeed_of_workEnergy (mi := 2) (qi := 1) (Vb := 9) (t₁ := 2 / 3)
    (by norm_num) (by norm_num) hφ continuous_const
    (fun t _ => PowerPorts.constForcePosition_hasDerivAt 2 0 0 9 t)
    (fun t _ => PowerPorts.constForceVelocity_hasDerivAt 2 0 9 t) (fun t _ => by norm_num)
    (by simp [PowerPorts.constForceVelocity]) ?_).2
  rw [hpos, PowerPorts.constForcePosition]
  norm_num

-- `2` ions per unit time of charge `1` carry the current `2`, so the beam mass flow is `2 · 2`.
example : beamMassFlow 2 1 2 = 2 * 2 :=
  beamMassFlow_of_current (by norm_num) (by norm_num)

-- Each ion of the fixture beam leaves with the kinetic energy `q_i V_b = 9`, and the beam carries
-- the kinetic power `ṁ v_e² / 2 = P_beam = 18`.
example :
    2 * ionExhaustSpeed 2 1 9 ^ 2 / 2 = 1 * 9 ∧
      beamMassFlow 2 1 2 * ionExhaustSpeed 2 1 9 ^ 2 / 2 = beamPower 9 2 :=
  beam_energy_port (by norm_num) (by norm_num) (by norm_num) 2

-- The fixture beam as a pressure-matched rocket (ambient and exit pressure `101325`, exit area
-- `1`): the separate-flow thrust is `54/5`, the effective exhaust velocity `γ_div v_e = 27/10`
-- and the specific impulse `(27/10) / g0` at `g0 = 9.80665`.
example :
    separateFlowThrust 0 0 0 0 (beamMassFlow 2 1 2) (ionExhaustSpeed 2 1 9 * (9 / 10)) 101325 1
        101325 = 54 / 5 ∧
      effectiveExhaustVelocity (ionThrust 2 1 9 2 (9 / 10)) (beamMassFlow 2 1 2) = 27 / 10 ∧
      specificImpulse (ionThrust 2 1 9 2 (9 / 10)) (beamMassFlow 2 1 2) 9.80665 =
        27 / 10 / 9.80665 := by
  obtain ⟨h1, h2, h3⟩ := ionThrust_eq_separateFlowThrust (mi := 2) (qi := 1) (Ib := 2)
    (by norm_num) (by norm_num) (by norm_num) 9 (9 / 10) 0 0 101325 1 9.80665
  have hv := ion_fixture.1
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1, ion_fixture.2.2.2.1]
  · rw [h2, hv]
    norm_num
  · rw [h3, hv]
    norm_num

-- The efficiency identity and bound at the fixture: `(18/20) (9/10)² ≤ 1`.
example :
    thrustEfficiency (ionThrust 2 1 9 2 (9 / 10)) (beamMassFlow 2 1 2) 20 =
        beamPower 9 2 / 20 * (9 / 10) ^ 2 ∧
      beamPower 9 2 / 20 * (9 / 10) ^ 2 ≤ 1 :=
  thrustEfficiency_eq_le_one (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [beamPower])

-- Xenon ions (molar mass `0.13129` kg/mol, charge number `1`) with the exact SI elementary charge
-- and Avogadro constant: the beam current `1` carries the molar flow `1 / F`, `F = e N_A`, and the
-- molar mass in place of the ion mass multiplies the mass flow by the factor `N_A`.
example :
    beamMassFlow (0.13129 / 6.02214076e23) (1 * 1.602176634e-19) 1 =
        1 / (1 * (1.602176634e-19 * 6.02214076e23)) * 0.13129 ∧
      beamMassFlow 0.13129 (1 * 1.602176634e-19) 1 =
        6.02214076e23 * beamMassFlow (0.13129 / 6.02214076e23) (1 * 1.602176634e-19) 1 :=
  beamMassFlow_molar (by norm_num) (by norm_num) (by norm_num)

-- Zero beam current: zero mass flow and a zero efficiency denominator at `P_in = 20`, while each
-- ion would still leave at a positive speed.
example :
    beamMassFlow 2 1 0 = 0 ∧ 2 * beamMassFlow 2 1 0 * 20 = 0 ∧ 0 < ionExhaustSpeed 2 1 9 :=
  zeroFlow_invalid (by norm_num) (by norm_num) (by norm_num) 20

end PhyslibExtTest.Mechanics.ElectricPropulsion
