/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.DistributedLineEnergy
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Circuits.DistributedLineEnergy

namespace PhyslibExtTest.Circuits.DistributedLineEnergy

/-- A lossless traveling wave carries power flux at the wave
speed `1/√(LC)` times the energy density, evaluated at a point
where the wave is nonzero: `L = C = 1`, `f = id`, `x = 2`,
`t = 0`. -/
example : powerFlux (travelingWaveVoltage 1 1 (fun x => x))
      (travelingWaveCurrent 1 1 (fun x => x)) 2 0
    = 1 / Real.sqrt (1 * 1) *
      energyDensity 1 1 (travelingWaveVoltage 1 1 (fun x => x))
        (travelingWaveCurrent 1 1 (fun x => x)) 2 0 :=
  travelingWave_powerFlux_eq_speed_mul_energyDensity 1 1 (fun x => x)
    (by norm_num) (by norm_num) 2 0

/-- For the same wave the electric and magnetic energy densities
agree at the nonzero point `x = 2`, `t = 0`. -/
example : (1 : ℝ) * travelingWaveVoltage 1 1 (fun x => x) 2 0 ^ 2 / 2
    = 1 * travelingWaveCurrent 1 1 (fun x => x) 2 0 ^ 2 / 2 :=
  travelingWave_electric_eq_magnetic 1 1 (fun x => x) (by norm_num)
    (by norm_num) 2 0

/-- Independent numeric check: for this wave both the power
flux and the energy density evaluate to `4` at `x = 2`, `t = 0`
(computed from the definitions, not from the library identity). -/
example : powerFlux (travelingWaveVoltage 1 1 (fun x => x))
    (travelingWaveCurrent 1 1 (fun x => x)) 2 0 = 4 := by
  simp [powerFlux, travelingWaveVoltage, travelingWaveCurrent]
  norm_num

example : energyDensity 1 1 (travelingWaveVoltage 1 1 (fun x => x))
    (travelingWaveCurrent 1 1 (fun x => x)) 2 0 = 4 := by
  simp [energyDensity, travelingWaveVoltage, travelingWaveCurrent]
  norm_num

/-- The integrated energy balance for the ramp wave on
`[0, 1] × [0, 1/2]`, with the correct endpoint order: the energy
change is `-1/4` (checked against the headline balance). -/
example : lineEnergy 1 1 1 (fun x t => x - t) (fun x t => x - t) (1 / 2)
    - lineEnergy 1 1 1 (fun x t => x - t) (fun x t => x - t) 0 = -1 / 4 := by
  have h := lineEnergy_sub_eq_integral_endpointFlux_sub_dissipation
    0 1 0 1 1 0 (1 / 2) Set.univ (fun x t => x - t) (fun x t => x - t)
    isOpen_univ (by fun_prop) (by fun_prop) rampWave_isTelegrapherSolution
    (by norm_num) (by norm_num) (Set.subset_univ _)
  rw [h]
  have hInt : (∫ s in (0 : ℝ)..(1 / 2),
        (powerFlux (fun x t => x - t) (fun x t => x - t) 0 s
          - powerFlux (fun x t => x - t) (fun x t => x - t) 1 s))
      = -1 / 4 := by
    have hfun : (fun s => powerFlux (fun x t => x - t) (fun x t => x - t) 0 s
        - powerFlux (fun x t => x - t) (fun x t => x - t) 1 s)
        = fun s => 2 * s - 1 := by
      ext s
      simp only [powerFlux]
      ring
    rw [hfun]
    rw [show (∫ s in (0 : ℝ)..(1 / 2), (2 * s - 1)) =
        (∫ s in (0 : ℝ)..(1 / 2), (2 * s)) - ∫ s in (0 : ℝ)..(1 / 2), (1 : ℝ) from
      intervalIntegral.integral_sub
        ((continuous_const.mul continuous_id).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const_mul, integral_id,
      intervalIntegral.integral_const]
    norm_num
  rw [hInt]
  simp [dissipationDensity]

/-- The shunt discharge loses stored energy strictly: the energy
at `t = 1` is below the energy at `t = 0`. -/
example : lineEnergy 1 1 1 (fun _ s => 1 * Real.exp (-(1 / 1) * s))
      (fun _ _ => 0) 1
    < lineEnergy 1 1 1 (fun _ s => 1 * Real.exp (-(1 / 1) * s))
      (fun _ _ => 0) 0 :=
  shuntDischarge_lineEnergy_strictAnti 1 1 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end PhyslibExtTest.Circuits.DistributedLineEnergy
