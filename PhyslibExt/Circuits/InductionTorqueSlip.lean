/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-!
# Induction machine torque and slip

## i. Overview

In the steady-state Thevenin equivalent of an induction machine, with
rotor resistance `R2` and synchronous mechanical speed `ws` positive,
stator Thevenin resistance `Rth` nonnegative, arbitrary real equivalent
reactance `Xeq`, and slip `s` in the motoring interval `(0, 1]`, the
rotor current is the Thevenin voltage divided by the complex impedance
whose real part is `Rth + R2 / s`. The air-gap power is three times the
squared current norm times `R2 / s`. Dividing by `ws` gives the
developed torque, which simplifies, after clearing the slip division,
to the rational function
`3 ‖Vth‖² R2 s / (ws ((Rth s + R2)² + (Xeq s)²))` of slip. That rational
curve is defined at zero slip, where it takes the value zero, and it is
continuous there. The converted mechanical power is the fraction
`1 - s` of the air-gap power, equivalently the torque times the rotor
speed `(1 - s) ws`, and the rotor copper loss is the complementary
fraction `s` of the air-gap power.

## ii. Key results

- `developedTorque_eq_torqueCurve`: the developed torque on the
  motoring interval equals the cleared rational torque curve.
- `torqueCurve_continuousAt_zero`: the rational curve extends
  continuously to zero at zero slip.
- `convertedPower_eq_torque_mul_rotorSpeed`: the converted power is
  the torque times the rotor speed, and is the `1 - s` fraction of the
  air-gap power.
- `inductionTorqueSlip_torque_andPowerBalance`: the combined torque,
  zero-slip, and power-split statement on the motoring interval.

## iii. Table of contents

- A. Rotor current and air-gap power
- B. Torque curve and zero-slip limit
- C. Converted power, copper loss, and power balance

## iv. References

- A. E. Fitzgerald, C. Kingsley Jr., and S. D. Umans, *Electric
  Machinery*, sixth edition, McGraw-Hill, 2003: the Thevenin
  equivalent of the induction machine, torque as air-gap power over
  synchronous speed, and the split of air-gap power into converted
  power and rotor copper loss by slip.

## A. Rotor current and air-gap power

## B. Torque curve and zero-slip limit

## C. Converted power, copper loss, and power balance
-/

@[expose] public section

namespace PhyslibExt.Circuits.InductionTorqueSlip

/-! ### A. Rotor current and air-gap power -/

/-- Rotor current in the Thevenin equivalent: the Thevenin voltage divided
by the impedance with real part `Rth + R2 / s` and reactance `Xeq`. Only
evaluated for nonzero slip. -/
noncomputable def rotorCurrent (Vth : ℂ) (Rth R2 Xeq s : ℝ) : ℂ :=
  Vth / ((↑(Rth + R2 / s) : ℂ) + (↑Xeq : ℂ) * Complex.I)

/-- Air-gap power: three times the squared current norm times the
slip-divided rotor resistance. -/
noncomputable def airGapPower (I2 : ℂ) (R2 s : ℝ) : ℝ :=
  3 * ‖I2‖ ^ 2 * (R2 / s)

/-- Developed torque at synchronous mechanical speed `ws`. -/
noncomputable def developedTorque (I2 : ℂ) (R2 s ws : ℝ) : ℝ :=
  airGapPower I2 R2 s / ws

/-- Squared norm of the rotor current, as the squared Thevenin voltage norm
divided by the squared impedance magnitude. The proof rewrites the complex
norm of the quotient through `Complex.normSq`. -/
lemma rotorCurrent_normSq (Vth : ℂ) (Rth R2 Xeq s : ℝ) (hs : s ≠ 0) :
    ‖rotorCurrent Vth Rth R2 Xeq s‖ ^ 2 =
      ‖Vth‖ ^ 2 / ((Rth + R2 / s) ^ 2 + Xeq ^ 2) := by
  unfold rotorCurrent
  rw [Complex.norm_div, div_pow]
  rw [← Complex.normSq_eq_norm_sq (((↑(Rth + R2 / s) : ℂ) + (↑Xeq : ℂ) * Complex.I))]
  rw [Complex.normSq_add_mul_I]

/-- Air-gap power in Thevenin quantities, before clearing the slip
division. -/
lemma airGapPower_eq (Vth : ℂ) (Rth R2 Xeq s : ℝ) (hs : s ≠ 0) :
    airGapPower (rotorCurrent Vth Rth R2 Xeq s) R2 s =
      3 * ‖Vth‖ ^ 2 * (R2 / s) / ((Rth + R2 / s) ^ 2 + Xeq ^ 2) := by
  unfold airGapPower
  rw [rotorCurrent_normSq Vth Rth R2 Xeq s hs]
  ring

/-! ### B. Torque curve and zero-slip limit -/

/-- The rational torque curve in slip, obtained by clearing the slip
division in the current formula. At zero slip its value is zero; the
rational form, not a totalized reciprocal, supplies that value. -/
noncomputable def torqueCurve (Vth : ℂ) (Rth R2 Xeq ws s : ℝ) : ℝ :=
  3 * ‖Vth‖ ^ 2 * R2 * s / (ws * ((Rth * s + R2) ^ 2 + (Xeq * s) ^ 2))

/-- Torque formula on the motoring interval: air-gap power over synchronous
speed equals the cleared rational function of slip. The proof clears the
slip division after rewriting `Rth + R2 / s` as `(Rth * s + R2) / s`, using
positivity of the resulting denominators. -/
theorem developedTorque_eq_torqueCurve (Vth : ℂ) (Rth R2 Xeq ws s : ℝ)
    (hR2 : 0 < R2) (hws : 0 < ws) (hRth : 0 ≤ Rth)
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    developedTorque (rotorCurrent Vth Rth R2 Xeq s) R2 s ws =
      3 * ‖Vth‖ ^ 2 * R2 * s / (ws * ((Rth * s + R2) ^ 2 + (Xeq * s) ^ 2)) := by
  have hs0' : s ≠ 0 := ne_of_gt hs0
  have hws' : ws ≠ 0 := ne_of_gt hws
  have hRs : 0 < Rth + R2 / s := by positivity
  have hA : 0 < Rth * s + R2 := by positivity
  have hD : (Rth + R2 / s) ^ 2 + Xeq ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hD' : (Rth * s + R2) ^ 2 + (Xeq * s) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hclear : Rth + R2 / s = (Rth * s + R2) / s := by
    field_simp
  have hD2 : ((Rth * s + R2) / s) ^ 2 + Xeq ^ 2 ≠ 0 := by
    rw [← hclear]
    exact hD
  unfold developedTorque
  rw [airGapPower_eq Vth Rth R2 Xeq s hs0', hclear]
  field_simp

/-- The rational curve agrees with its defining expression in `torqueCurve`
on the motoring interval. -/
lemma torqueCurve_eq_developedTorque (Vth : ℂ) (Rth R2 Xeq ws s : ℝ)
    (hR2 : 0 < R2) (hws : 0 < ws) (hRth : 0 ≤ Rth)
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    torqueCurve Vth Rth R2 Xeq ws s =
      developedTorque (rotorCurrent Vth Rth R2 Xeq s) R2 s ws := by
  have h := developedTorque_eq_torqueCurve Vth Rth R2 Xeq ws s hR2 hws hRth hs0 hs1
  unfold torqueCurve
  exact h.symm

/-- Zero-slip value of the rational torque curve. -/
lemma torqueCurve_zero (Vth : ℂ) (Rth R2 Xeq ws : ℝ)
    (hR2 : 0 < R2) (hws : 0 < ws) (hRth : 0 ≤ Rth) :
    torqueCurve Vth Rth R2 Xeq ws 0 = 0 := by
  simp [torqueCurve]

/-- Continuous extension to zero slip: the rational torque curve is
continuous at zero and takes the value zero there. Continuity follows from
continuity of the numerator and denominator, with the denominator at zero
slip reducing to `ws * R2 ^ 2`, which is nonzero. -/
theorem torqueCurve_continuousAt_zero (Vth : ℂ) (Rth R2 Xeq ws : ℝ)
    (hR2 : 0 < R2) (hws : 0 < ws) (hRth : 0 ≤ Rth) :
    ContinuousAt (fun s : ℝ => torqueCurve Vth Rth R2 Xeq ws s) 0 ∧
      torqueCurve Vth Rth R2 Xeq ws 0 = 0 := by
  constructor
  · simp only [torqueCurve]
    apply ContinuousAt.div₀
    · fun_prop
    · fun_prop
    · show ws * ((Rth * 0 + R2) ^ 2 + (Xeq * 0) ^ 2) ≠ 0
      have h1 : (Rth * 0 + R2) ^ 2 + (Xeq * 0) ^ 2 = R2 ^ 2 := by simp
      rw [h1]
      exact ne_of_gt (mul_pos hws (pow_pos hR2 2))
  · exact torqueCurve_zero Vth Rth R2 Xeq ws hR2 hws hRth

/-- Standstill validation case: at unit slip the torque is the rational
curve evaluated at one. -/
lemma torque_at_standstill (Vth : ℂ) (Rth R2 Xeq ws : ℝ)
    (hR2 : 0 < R2) (hws : 0 < ws) (hRth : 0 ≤ Rth) :
    developedTorque (rotorCurrent Vth Rth R2 Xeq 1) R2 1 ws =
      3 * ‖Vth‖ ^ 2 * R2 / (ws * ((Rth + R2) ^ 2 + Xeq ^ 2)) := by
  have h := developedTorque_eq_torqueCurve Vth Rth R2 Xeq ws 1 hR2 hws hRth
    zero_lt_one (le_refl 1)
  simpa using h

/-! ### C. Converted power, copper loss, and power balance -/

/-- Converted mechanical power at slip `s`: the fraction `1 - s` of the
air-gap power. -/
noncomputable def convertedPower (I2 : ℂ) (R2 s : ℝ) : ℝ :=
  (1 - s) * airGapPower I2 R2 s

/-- Rotor copper loss at slip `s`: the fraction `s` of the air-gap power. -/
noncomputable def rotorCopperLoss (I2 : ℂ) (R2 s : ℝ) : ℝ :=
  s * airGapPower I2 R2 s

/-- Power split: air-gap power is converted power plus rotor copper loss,
for any slip at which the air-gap power is formed. -/
lemma airGapPower_eq_converted_add_copper (I2 : ℂ) (R2 s : ℝ) :
    airGapPower I2 R2 s = convertedPower I2 R2 s + rotorCopperLoss I2 R2 s := by
  unfold convertedPower rotorCopperLoss
  ring

/-- Converted power is torque times rotor speed `(1 - s) * ws`, for
positive slip. The first component is field simplification after unfolding
the definitions; the other two are the defining fractions. -/
theorem convertedPower_eq_torque_mul_rotorSpeed (Vth : ℂ) (Rth R2 Xeq ws s : ℝ)
    (hR2 : 0 < R2) (hws : 0 < ws) (hRth : 0 ≤ Rth)
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    convertedPower (rotorCurrent Vth Rth R2 Xeq s) R2 s =
      developedTorque (rotorCurrent Vth Rth R2 Xeq s) R2 s ws * ((1 - s) * ws) ∧
      convertedPower (rotorCurrent Vth Rth R2 Xeq s) R2 s =
        (1 - s) * airGapPower (rotorCurrent Vth Rth R2 Xeq s) R2 s ∧
      rotorCopperLoss (rotorCurrent Vth Rth R2 Xeq s) R2 s =
        s * airGapPower (rotorCurrent Vth Rth R2 Xeq s) R2 s := by
  have hws' : ws ≠ 0 := ne_of_gt hws
  refine ⟨?_, rfl, rfl⟩
  unfold convertedPower developedTorque
  field_simp

/-- Headline result: on the motoring interval the torque equals the cleared
rational curve, the curve extends continuously to zero at zero slip, and
the air-gap power splits into converted power at the rotor speed and rotor
copper loss. -/
theorem inductionTorqueSlip_torque_andPowerBalance (Vth : ℂ) (Rth R2 Xeq ws s : ℝ)
    (hR2 : 0 < R2) (hws : 0 < ws) (hRth : 0 ≤ Rth)
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    developedTorque (rotorCurrent Vth Rth R2 Xeq s) R2 s ws =
        3 * ‖Vth‖ ^ 2 * R2 * s / (ws * ((Rth * s + R2) ^ 2 + (Xeq * s) ^ 2)) ∧
      torqueCurve Vth Rth R2 Xeq ws 0 = 0 ∧
      ContinuousAt (fun t : ℝ => torqueCurve Vth Rth R2 Xeq ws t) 0 ∧
      convertedPower (rotorCurrent Vth Rth R2 Xeq s) R2 s =
        (1 - s) * airGapPower (rotorCurrent Vth Rth R2 Xeq s) R2 s ∧
      convertedPower (rotorCurrent Vth Rth R2 Xeq s) R2 s =
        developedTorque (rotorCurrent Vth Rth R2 Xeq s) R2 s ws * ((1 - s) * ws) ∧
      rotorCopperLoss (rotorCurrent Vth Rth R2 Xeq s) R2 s =
        s * airGapPower (rotorCurrent Vth Rth R2 Xeq s) R2 s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact developedTorque_eq_torqueCurve Vth Rth R2 Xeq ws s hR2 hws hRth hs0 hs1
  · exact torqueCurve_zero Vth Rth R2 Xeq ws hR2 hws hRth
  · exact (torqueCurve_continuousAt_zero Vth Rth R2 Xeq ws hR2 hws hRth).1
  · exact (convertedPower_eq_torque_mul_rotorSpeed Vth Rth R2 Xeq ws s hR2 hws hRth
      hs0 hs1).2.1
  · exact (convertedPower_eq_torque_mul_rotorSpeed Vth Rth R2 Xeq ws s hR2 hws hRth
      hs0 hs1).1
  · exact (convertedPower_eq_torque_mul_rotorSpeed Vth Rth R2 Xeq ws s hR2 hws hRth
      hs0 hs1).2.2

end PhyslibExt.Circuits.InductionTorqueSlip
