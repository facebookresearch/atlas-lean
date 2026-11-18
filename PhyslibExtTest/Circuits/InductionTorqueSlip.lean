/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.InductionTorqueSlip
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Complex.Basic

@[expose] public section

open PhyslibExt.Circuits.InductionTorqueSlip

namespace PhyslibExtTest.Circuits.InductionTorqueSlip

/-- Standstill torque at unit phasor, `Rth = 0`, `R2 = 1`, `Xeq = 1`,
`ws = 3`: `3 / (3 * (1 ^ 2 + 1 ^ 2)) = 1 / 2`. -/
example :
    developedTorque (rotorCurrent (1 : ℂ) 0 1 1 1) 1 1 3 = 1 / 2 := by
  have h := torque_at_standstill (1 : ℂ) 0 1 1 3 (by norm_num) (by norm_num)
    (by norm_num)
  simp only [norm_one] at h
  norm_num at h
  exact h

/-- Zero-slip value of the rational torque curve at the same parameters. -/
example : torqueCurve (1 : ℂ) 0 1 1 3 0 = 0 :=
  torqueCurve_zero (1 : ℂ) 0 1 1 3 (by norm_num) (by norm_num) (by norm_num)

/-- The rational torque curve is continuous at zero slip. -/
example : ContinuousAt (fun s : ℝ => torqueCurve (1 : ℂ) 0 1 1 3 s) 0 :=
  (torqueCurve_continuousAt_zero (1 : ℂ) 0 1 1 3 (by norm_num) (by norm_num)
    (by norm_num)).1

/-- Power split at unit current, `R2 = 1`, `s = 3 / 8`: the air-gap power
`8` splits into converted power `5` and rotor copper loss `3`. -/
example :
    airGapPower (1 : ℂ) 1 (3 / 8) =
      convertedPower (1 : ℂ) 1 (3 / 8) + rotorCopperLoss (1 : ℂ) 1 (3 / 8) :=
  airGapPower_eq_converted_add_copper (1 : ℂ) 1 (3 / 8)

example : airGapPower (1 : ℂ) 1 (3 / 8) = 8 := by
  have h : ‖(1 : ℂ)‖ = (1 : ℝ) := norm_one
  unfold airGapPower
  rw [h]
  norm_num

example : convertedPower (1 : ℂ) 1 (3 / 8) = 5 := by
  have h : ‖(1 : ℂ)‖ = (1 : ℝ) := norm_one
  unfold convertedPower rotorCopperLoss airGapPower
  rw [h]
  norm_num

example : rotorCopperLoss (1 : ℂ) 1 (3 / 8) = 3 := by
  have h : ‖(1 : ℂ)‖ = (1 : ℝ) := norm_one
  unfold rotorCopperLoss
  rw [h]
  norm_num

/-- Air-gap power at the same values, through the canonical per-phase
complex power for the voltage across the slip-divided resistance. -/
example :
    airGapPower (1 : ℂ) 1 (3 / 8) =
      3 * (PhyslibExt.Circuits.BalancedThreePhase.complexPower
        (((1 / (3 / 8) : ℝ) : ℂ) * (1 : ℂ)) (1 : ℂ)).re :=
  airGapPower_eq_three_mul_re_complexPower (1 : ℂ) 1 (3 / 8)

/-- Converted power at rotor speed, on a motoring-interval example. -/
example :
    convertedPower (rotorCurrent (1 : ℂ) 0 1 1 (1 / 2)) 1 (1 / 2) =
      developedTorque (rotorCurrent (1 : ℂ) 0 1 1 (1 / 2)) 1 (1 / 2) 3 *
        ((1 - 1 / 2) * 3) :=
  (convertedPower_eq_torque_mul_rotorSpeed (1 : ℂ) 0 1 1 3 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1

/-- Zero-slip boundary: with `Vth = 1`, `Rth = 1`, `R2 = 1`, `Xeq = 0`, the
rotor current at zero slip is zero, not the totalized quotient `1`. -/
example : rotorCurrent (1 : ℂ) 1 1 0 0 = 0 :=
  rotorCurrent_zero_slip (1 : ℂ) 1 1 0

/-- At zero slip the model's air-gap power, copper loss, and converted power
vanish, and the torque equals the rational curve's zero-slip value `0`. -/
example :
    airGapPower (rotorCurrent (1 : ℂ) 1 1 0 0) 1 0 = 0 ∧
      rotorCopperLoss (rotorCurrent (1 : ℂ) 1 1 0 0) 1 0 = 0 ∧
      convertedPower (rotorCurrent (1 : ℂ) 1 1 0 0) 1 0 = 0 ∧
      developedTorque (rotorCurrent (1 : ℂ) 1 1 0 0) 1 0 3 = 0 := by
  obtain ⟨-, hag, hcu, hcv, htq⟩ := rotorQuantities_zero_slip (1 : ℂ) 1 1 0 3
  refine ⟨hag, hcu, hcv, ?_⟩
  rw [htq]
  exact torqueCurve_zero (1 : ℂ) 1 1 0 3 (by norm_num) (by norm_num) (by norm_num)

/-- At nonzero slip the cleared current is the Thevenin quotient. -/
example :
    rotorCurrent (1 : ℂ) 0 1 1 (1 / 2) =
      1 / ((↑((0 : ℝ) + 1 / (1 / 2)) : ℂ) + (↑(1 : ℝ) : ℂ) * Complex.I) :=
  rotorCurrent_eq_div (1 : ℂ) 0 1 1 (1 / 2) (by norm_num)

/-- Power split at a generating slip `s = -1 / 2`, for an independently
given unit current, `R2 = 1`, `ws = 3`: the copper loss is the `s`
fraction of the air-gap power `-6`. -/
example :
    rotorCopperLoss (1 : ℂ) 1 (-1 / 2) = (-1 / 2) * airGapPower (1 : ℂ) 1 (-1 / 2) :=
  (powerSplit_of_ne_zero (1 : ℂ) 1 (-1 / 2) 3 (by norm_num) (by norm_num)).2.2

example : airGapPower (1 : ℂ) 1 (-1 / 2) = -6 := by
  have h : ‖(1 : ℂ)‖ = (1 : ℝ) := norm_one
  unfold airGapPower
  rw [h]
  norm_num

/-- Converted power at the generating slip: torque times rotor speed
`(1 - s) * ws` with `s = -1 / 2`. -/
example :
    convertedPower (1 : ℂ) 1 (-1 / 2) =
      developedTorque (1 : ℂ) 1 (-1 / 2) 3 * ((1 - -1 / 2) * 3) :=
  (powerSplit_of_ne_zero (1 : ℂ) 1 (-1 / 2) 3 (by norm_num) (by norm_num)).1

end PhyslibExtTest.Circuits.InductionTorqueSlip
