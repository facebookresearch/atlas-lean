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
speed `1/√(LC)` times the energy density: here `L = C = 1` at the
origin. -/
example : powerFlux (travelingWaveVoltage 1 1 (fun x => x))
      (travelingWaveCurrent 1 1 (fun x => x)) 0 0
    = 1 / Real.sqrt (1 * 1) *
      energyDensity 1 1 (travelingWaveVoltage 1 1 (fun x => x))
        (travelingWaveCurrent 1 1 (fun x => x)) 0 0 :=
  travelingWave_powerFlux_eq_speed_mul_energyDensity 1 1 (fun x => x)
    (by norm_num) (by norm_num) 0 0

/-- The shunt discharge loses stored energy strictly: the energy
at `t = 1` is below the energy at `t = 0`. -/
example : lineEnergy 1 1 1 (fun _ s => 1 * Real.exp (-(1 / 1) * s))
      (fun _ _ => 0) 1
    < lineEnergy 1 1 1 (fun _ s => 1 * Real.exp (-(1 / 1) * s))
      (fun _ _ => 0) 0 :=
  shuntDischarge_lineEnergy_strictAnti 1 1 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end PhyslibExtTest.Circuits.DistributedLineEnergy
