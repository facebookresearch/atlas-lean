/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import PhyslibExt.Circuits.BalancedThreePhase
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
whose real part is `Rth + R2 / s`. The current is defined in the
equivalent cleared form `Vth s / (Rth s + R2 + i Xeq s)`, which agrees
with that quotient at every nonzero slip and vanishes at zero slip, the
synchronous-speed state with no rotor current. The air-gap power is three times the
squared current norm times `R2 / s`. Dividing by `ws` gives the
developed torque, which simplifies, after clearing the slip division,
to the rational function
`3 ‖Vth‖² R2 s / (ws ((Rth s + R2)² + (Xeq s)²))` of slip. That rational
curve is defined at zero slip, where it takes the value zero, and it is
continuous there. The rotor copper loss is defined independently, as
the three-phase resistive loss `3 ‖I2‖² R2` in the rotor resistance,
and the converted mechanical power is the air-gap power remaining
after that loss. For nonzero slip these definitions give the familiar
fractions: the converted power is the fraction `1 - s` of the air-gap
power, equivalently the torque times the rotor speed `(1 - s) ws`, and
the rotor copper loss is the complementary fraction `s` of the
air-gap power. These fractional identities hold for any rotor current
at any nonzero slip, so they also cover generating slips. At zero slip
the model's current, powers, and torque all vanish.

## ii. Key results

- `developedTorque_eq_torqueCurve`: the developed torque on the
  motoring interval equals the cleared rational torque curve.
- `torqueCurve_continuousAt_zero`: the rational curve extends
  continuously to zero at zero slip.
- `airGapPower_eq_three_mul_re_complexPower`: the air-gap power is
  three times the real part of the canonical per-phase complex power
  for the voltage across the slip-divided rotor resistance.
- `powerSplit_of_ne_zero`: for any rotor current at nonzero slip and
  nonzero synchronous speed, the converted power is the torque times
  the rotor speed and the `1 - s` fraction of the air-gap power, and
  the copper loss is the `s` fraction.
- `convertedPower_eq_torque_mul_rotorSpeed`: the same split for the
  model current on the motoring interval.
- `rotorQuantities_zero_slip`: at zero slip the model current, air-gap
  power, copper loss, and converted power vanish, and the torque equals
  the rational curve's zero-slip value.
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

open ComplexConjugate

/-! ### A. Rotor current and air-gap power -/

/-- Rotor current in the Thevenin equivalent: the Thevenin voltage divided
by the impedance with real part `Rth + R2 / s` and reactance `Xeq`. It is
written with the slip division cleared, as `Vth s / (Rth s + R2 + i Xeq s)`,
so that no reciprocal of the slip appears: at nonzero slip it equals the
quotient (`rotorCurrent_eq_div`), and at zero slip it is zero
(`rotorCurrent_zero_slip`), the physical value at synchronous speed. -/
noncomputable def rotorCurrent (Vth : ℂ) (Rth R2 Xeq s : ℝ) : ℂ :=
  Vth * (s : ℂ) / ((↑(Rth * s + R2) : ℂ) + (↑(Xeq * s) : ℂ) * Complex.I)

/-- At nonzero slip the rotor current is the Thevenin voltage divided by
the impedance with real part `Rth + R2 / s` and reactance `Xeq`. The
proof multiplies that impedance by `s`. -/
lemma rotorCurrent_eq_div (Vth : ℂ) (Rth R2 Xeq s : ℝ) (hs : s ≠ 0) :
    rotorCurrent Vth Rth R2 Xeq s =
      Vth / ((↑(Rth + R2 / s) : ℂ) + (↑Xeq : ℂ) * Complex.I) := by
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hden : (↑(Rth * s + R2) : ℂ) + (↑(Xeq * s) : ℂ) * Complex.I =
      ((↑(Rth + R2 / s) : ℂ) + (↑Xeq : ℂ) * Complex.I) * (s : ℂ) := by
    push_cast
    field_simp
  unfold rotorCurrent
  rw [hden, mul_div_mul_right _ _ hs']

/-- At zero slip the rotor current is zero. -/
lemma rotorCurrent_zero_slip (Vth : ℂ) (Rth R2 Xeq : ℝ) :
    rotorCurrent Vth Rth R2 Xeq 0 = 0 := by
  simp [rotorCurrent]

/-- Air-gap power: three times the squared current norm times the
slip-divided rotor resistance. The physical statements about it assume
nonzero slip; at zero slip the model current is zero
(`rotorCurrent_zero_slip`), so the air-gap power of the model vanishes
there, and a nonzero current paired with zero slip is not a state of the
model. -/
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
  rw [rotorCurrent_eq_div Vth Rth R2 Xeq s hs, Complex.norm_div, div_pow]
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

/-- Air-gap power through the canonical per-phase complex power: for the
voltage `((R2 / s : ℝ) : ℂ) * I2` across the slip-divided rotor resistance,
the canonical complex power
`PhyslibExt.Circuits.BalancedThreePhase.complexPower` (RMS phasors, passive
sign convention) has real part `(R2 / s) * ‖I2‖²`, and the three-phase
air-gap power is three times that real part. -/
lemma airGapPower_eq_three_mul_re_complexPower (I2 : ℂ) (R2 s : ℝ) :
    airGapPower I2 R2 s =
      3 * (PhyslibExt.Circuits.BalancedThreePhase.complexPower
        (((R2 / s : ℝ) : ℂ) * I2) I2).re := by
  have h : PhyslibExt.Circuits.BalancedThreePhase.complexPower
        (((R2 / s : ℝ) : ℂ) * I2) I2 = ((R2 / s * ‖I2‖ ^ 2 : ℝ) : ℂ) := by
    unfold PhyslibExt.Circuits.BalancedThreePhase.complexPower
    rw [show ((↑(R2 / s) * I2) * conj I2) = ↑(R2 / s) * (I2 * conj I2) by ring,
      Complex.mul_conj']
    push_cast
    ring
  unfold airGapPower
  rw [h, Complex.ofReal_re]
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

/-- Rotor copper loss: the three-phase resistive loss `3 ‖I2‖² R2` in
the rotor resistance `R2`, at rotor current `I2`. It is defined from the
current and the resistance alone; the slip argument is kept so that the
loss, the air-gap power, and the converted power share one calling
convention. -/
noncomputable def rotorCopperLoss (I2 : ℂ) (R2 s : ℝ) : ℝ :=
  3 * ‖I2‖ ^ 2 * R2

/-- Converted mechanical power: the air-gap power remaining after the
rotor copper loss. It is defined as that difference; its expression as
the fraction `1 - s` of the air-gap power is a theorem for nonzero
slip, proved in `convertedPower_eq_torque_mul_rotorSpeed`. -/
noncomputable def convertedPower (I2 : ℂ) (R2 s : ℝ) : ℝ :=
  airGapPower I2 R2 s - rotorCopperLoss I2 R2 s

/-- Power split: air-gap power is converted power plus rotor copper loss,
for any slip at which the air-gap power is formed. Expanding all three
quantities gives the air-gap term `3 ‖I2‖² (R2 / s)` on the left and
that same term, minus and plus the copper term `3 ‖I2‖² R2`, on the
right. -/
lemma airGapPower_eq_converted_add_copper (I2 : ℂ) (R2 s : ℝ) :
    airGapPower I2 R2 s = convertedPower I2 R2 s + rotorCopperLoss I2 R2 s := by
  unfold convertedPower rotorCopperLoss airGapPower
  ring

/-- Power split for any rotor current `I2`, at any nonzero slip and nonzero
synchronous speed, motoring or generating: the converted power is the
torque times the rotor speed `(1 - s) * ws` and the fraction `1 - s` of
the air-gap power, and the rotor copper loss is the fraction `s`. With
`s ≠ 0`, the copper term `3 ‖I2‖² R2` is `s` times the air-gap term
`3 ‖I2‖² (R2 / s)`, and the remaining difference is `1 - s` times that
air-gap term. The torque form then follows from `developedTorque`, using
`ws ≠ 0`. -/
theorem powerSplit_of_ne_zero (I2 : ℂ) (R2 s ws : ℝ) (hs : s ≠ 0) (hws : ws ≠ 0) :
    convertedPower I2 R2 s = developedTorque I2 R2 s ws * ((1 - s) * ws) ∧
      convertedPower I2 R2 s = (1 - s) * airGapPower I2 R2 s ∧
      rotorCopperLoss I2 R2 s = s * airGapPower I2 R2 s := by
  have hsr : s * (R2 / s) = R2 := mul_div_cancel₀ R2 hs
  have hcop : rotorCopperLoss I2 R2 s = s * airGapPower I2 R2 s := by
    unfold rotorCopperLoss airGapPower
    rw [show s * (3 * ‖I2‖ ^ 2 * (R2 / s)) = (3 * ‖I2‖ ^ 2) * (s * (R2 / s)) by ring,
      hsr]
  have hconv : convertedPower I2 R2 s = (1 - s) * airGapPower I2 R2 s := by
    have hfrac : (1 - s) * (R2 / s) = R2 / s - R2 := by
      rw [sub_mul, one_mul, hsr]
    unfold convertedPower rotorCopperLoss airGapPower
    rw [show (1 - s) * (3 * ‖I2‖ ^ 2 * (R2 / s)) = (3 * ‖I2‖ ^ 2) * ((1 - s) * (R2 / s)) by
      ring, hfrac]
    ring
  refine ⟨?_, hconv, hcop⟩
  rw [hconv]
  unfold developedTorque
  field_simp

/-- Converted power is torque times rotor speed `(1 - s) * ws`, for the
model current on the motoring interval. This is `powerSplit_of_ne_zero`
specialized to that current; it uses only `s ≠ 0` and `ws ≠ 0`, and keeps
the motoring hypotheses shared by the other results of this file. -/
theorem convertedPower_eq_torque_mul_rotorSpeed (Vth : ℂ) (Rth R2 Xeq ws s : ℝ)
    (hR2 : 0 < R2) (hws : 0 < ws) (hRth : 0 ≤ Rth)
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    convertedPower (rotorCurrent Vth Rth R2 Xeq s) R2 s =
      developedTorque (rotorCurrent Vth Rth R2 Xeq s) R2 s ws * ((1 - s) * ws) ∧
      convertedPower (rotorCurrent Vth Rth R2 Xeq s) R2 s =
        (1 - s) * airGapPower (rotorCurrent Vth Rth R2 Xeq s) R2 s ∧
      rotorCopperLoss (rotorCurrent Vth Rth R2 Xeq s) R2 s =
        s * airGapPower (rotorCurrent Vth Rth R2 Xeq s) R2 s :=
  powerSplit_of_ne_zero _ R2 s ws (ne_of_gt hs0) (ne_of_gt hws)

/-- Zero-slip boundary of the model: the rotor current is zero, so the
air-gap power, rotor copper loss, and converted power vanish, and the
developed torque equals the rational curve's zero-slip value. -/
lemma rotorQuantities_zero_slip (Vth : ℂ) (Rth R2 Xeq ws : ℝ) :
    rotorCurrent Vth Rth R2 Xeq 0 = 0 ∧
      airGapPower (rotorCurrent Vth Rth R2 Xeq 0) R2 0 = 0 ∧
      rotorCopperLoss (rotorCurrent Vth Rth R2 Xeq 0) R2 0 = 0 ∧
      convertedPower (rotorCurrent Vth Rth R2 Xeq 0) R2 0 = 0 ∧
      developedTorque (rotorCurrent Vth Rth R2 Xeq 0) R2 0 ws =
        torqueCurve Vth Rth R2 Xeq ws 0 := by
  rw [rotorCurrent_zero_slip]
  simp [airGapPower, rotorCopperLoss, convertedPower, developedTorque, torqueCurve]

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
