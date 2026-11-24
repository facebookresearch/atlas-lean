/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.BalancedThreePhase
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Synchronous generator power and angle

## i. Overview

In the lossless synchronous-generator phasor model, with positive
real internal voltage magnitude `E`, terminal voltage magnitude `V`,
and synchronous reactance `Xs`, and with generator current directed
out toward the bus, the current is the difference between the
internal voltage phasor at load angle `delta` and the terminal
voltage phasor, divided by the purely reactive impedance `i * Xs`.
The three-phase complex power formed from the terminal voltage and
the conjugate current, in the RMS convention, has real part
`3 * V * E * sin delta / Xs` and reactive part
`3 * V * (E * cos delta - V) / Xs`. The current is first rewritten
in rectangular form, with sine and cosine components over `Xs`, and
the two power formulas are then read off from the real and imaginary
parts of `3 * V * conj I`, where the per-phase factor is the
`complexPower` of `PhyslibExt.Circuits.BalancedThreePhase`.

## ii. Key results

- `synchronousGenerator_powerAngle`: the combined real-power,
  reactive-power, and current-model statement.
- `realPower_eq`: real power `3 * V * E * sin delta / Xs`.
- `reactivePower_eq`: reactive power
  `3 * V * (E * cos delta - V) / Xs`.
- `synchronousCurrent_eq`: the current in rectangular form.
- `power_at_zero_angle`, `realPower_pos_of_angle_pos`, and
  `totalComplexPower_neg_current`: the zero-angle, positive-angle,
  and reversed-current validation cases.

## iii. Table of contents

- A. Synchronous current and complex power
- B. Power-angle formulas
- C. Validation cases

## iv. References

- A. E. Fitzgerald, C. Kingsley Jr., and S. D. Umans, *Electric
  Machinery*, sixth edition, McGraw-Hill, 2003: synchronous-machine
  phasor model and the power-angle relation.

## A. Synchronous current and complex power
-/

@[expose] public section

namespace PhyslibExt.Circuits.SynchronousPowerAngle

/-- Generator current directed out toward the bus: the internal phasor at
load angle minus the real terminal voltage, over the reactive impedance. -/
noncomputable def synchronousCurrent (E V Xs delta : ℝ) : ℂ :=
  (((↑E : ℂ) * Complex.exp ((↑delta : ℂ) * Complex.I) - (↑V : ℂ)) /
    ((↑Xs : ℂ) * Complex.I))

/-- Three-phase complex power at the terminals: three times the per-phase
RMS complex power of the terminal voltage phasor and the current. -/
noncomputable def totalComplexPower (V : ℝ) (I : ℂ) : ℂ :=
  3 * PhyslibExt.Circuits.BalancedThreePhase.complexPower (↑V : ℂ) I

/-- Terminal real power: the real part of the three-phase complex power. -/
noncomputable def realPower (E V Xs delta : ℝ) : ℝ :=
  (totalComplexPower V (synchronousCurrent E V Xs delta)).re

/-- Terminal reactive power: the imaginary part of the three-phase complex
power. -/
noncomputable def reactivePower (E V Xs delta : ℝ) : ℝ :=
  (totalComplexPower V (synchronousCurrent E V Xs delta)).im

/-- Current in rectangular form: the sine component over the reactance in
the real part, and the terminal-minus-cosine component over the reactance
in the imaginary part. -/
lemma synchronousCurrent_eq (E V Xs delta : ℝ) (hXs : 0 < Xs) :
    synchronousCurrent E V Xs delta =
      ((↑(E * Real.sin delta / Xs) : ℂ) +
        (↑((V - E * Real.cos delta) / Xs) : ℂ) * Complex.I) := by
  have hXsne : Xs ≠ 0 := ne_of_gt hXs
  have hXsc : ((↑Xs : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hXsne) Complex.I_ne_zero
  unfold synchronousCurrent
  rw [div_eq_iff hXsc, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.mul_im,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    field_simp
    ring
  · simp only [Complex.mul_re, Complex.add_re, Complex.sub_im, Complex.mul_im,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    field_simp
    ring

/-! ## B. Power-angle formulas -/

/-- Real power angle formula: three times the voltage product times the
sine of the load angle over the synchronous reactance. -/
theorem realPower_eq (E V Xs delta : ℝ)
    (hE : 0 < E) (hV : 0 < V) (hXs : 0 < Xs) :
    realPower E V Xs delta = 3 * V * E * Real.sin delta / Xs := by
  have h3 : (3 : ℂ) = ((3 : ℝ) : ℂ) := (Complex.ofReal_ofNat 3).symm
  unfold realPower totalComplexPower PhyslibExt.Circuits.BalancedThreePhase.complexPower
  rw [synchronousCurrent_eq E V Xs delta hXs, h3]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- Reactive power angle formula: three times the terminal voltage times
the cosine term minus the terminal voltage, over the reactance. -/
theorem reactivePower_eq (E V Xs delta : ℝ)
    (hE : 0 < E) (hV : 0 < V) (hXs : 0 < Xs) :
    reactivePower E V Xs delta = 3 * V * (E * Real.cos delta - V) / Xs := by
  have h3 : (3 : ℂ) = ((3 : ℝ) : ℂ) := (Complex.ofReal_ofNat 3).symm
  unfold reactivePower totalComplexPower PhyslibExt.Circuits.BalancedThreePhase.complexPower
  rw [synchronousCurrent_eq E V Xs delta hXs, h3]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- Complex power in rectangular form: its real and imaginary parts are
the two power angle formulas. -/
lemma totalComplexPower_eq (E V Xs delta : ℝ)
    (hE : 0 < E) (hV : 0 < V) (hXs : 0 < Xs) :
    (totalComplexPower V (synchronousCurrent E V Xs delta)).re =
        3 * V * E * Real.sin delta / Xs ∧
      (totalComplexPower V (synchronousCurrent E V Xs delta)).im =
        3 * V * (E * Real.cos delta - V) / Xs := by
  exact ⟨realPower_eq E V Xs delta hE hV hXs,
    reactivePower_eq E V Xs delta hE hV hXs⟩

/-- Headline result: from the generator current model and the RMS complex
power convention, the terminal real and reactive three-phase powers are
the sine and cosine power angle formulas. -/
theorem synchronousGenerator_powerAngle (E V Xs delta : ℝ)
    (hE : 0 < E) (hV : 0 < V) (hXs : 0 < Xs) :
    (totalComplexPower V (synchronousCurrent E V Xs delta)).re =
        3 * V * E * Real.sin delta / Xs ∧
      (totalComplexPower V (synchronousCurrent E V Xs delta)).im =
        3 * V * (E * Real.cos delta - V) / Xs ∧
      synchronousCurrent E V Xs delta =
        (((↑E : ℂ) * Complex.exp ((↑delta : ℂ) * Complex.I) - (↑V : ℂ)) /
          ((↑Xs : ℂ) * Complex.I)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (totalComplexPower_eq E V Xs delta hE hV hXs).1
  · exact (totalComplexPower_eq E V Xs delta hE hV hXs).2
  · rfl

/-! ## C. Validation cases -/

/-- Zero load angle validation case: no real power is transferred, and the
reactive power is the zero-angle cosine formula. -/
lemma power_at_zero_angle (E V Xs : ℝ)
    (hE : 0 < E) (hV : 0 < V) (hXs : 0 < Xs) :
    realPower E V Xs 0 = 0 ∧
      reactivePower E V Xs 0 = 3 * V * (E - V) / Xs := by
  constructor
  · rw [realPower_eq E V Xs 0 hE hV hXs, Real.sin_zero]
    ring
  · rw [reactivePower_eq E V Xs 0 hE hV hXs, Real.cos_zero]
    ring

/-- Positive small angle validation case: for a load angle strictly
between zero and pi, the real power is positive. -/
lemma realPower_pos_of_angle_pos (E V Xs delta : ℝ)
    (hE : 0 < E) (hV : 0 < V) (hXs : 0 < Xs)
    (hd0 : 0 < delta) (hdpi : delta < Real.pi) :
    0 < realPower E V Xs delta := by
  rw [realPower_eq E V Xs delta hE hV hXs]
  have hsin : 0 < Real.sin delta := Real.sin_pos_of_pos_of_lt_pi hd0 hdpi
  positivity

/-- Reversing the current convention negates both terminal powers: the
complex power formed with the negated current is the negation. -/
lemma totalComplexPower_neg_current (V : ℝ) (I : ℂ) :
    totalComplexPower V (-I) = -totalComplexPower V I := by
  unfold totalComplexPower PhyslibExt.Circuits.BalancedThreePhase.complexPower
  simp only [map_neg]
  ring

end PhyslibExt.Circuits.SynchronousPowerAngle
