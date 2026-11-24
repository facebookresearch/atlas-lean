/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# RMS phasor average power

## i. Overview

For complex phasor amplitudes `V` and `I` and angular frequency
`omega > 0`, the RMS waveforms are the real signals
`t ↦ sqrt 2 * Re(V * exp(i * omega * t))` in RMS scaling. Their
product averages over any full period `2 * pi / omega` to
`Re(V * conj(I))`: the standard average-power formula. The peak
(unscaled) waveforms average to half that value. The in-phase case
gives `|V|^2` for a waveform against itself, and a quadrature
current (`I * V` in place of `V`) averages to zero. No impedance,
network or load model is introduced.

## ii. Key results

- `average_rmsWaveform_mul_rmsWaveform`: the average of the product
  of two RMS waveforms over a full period is `Re(V * conj I)`.
- `average_rmsWaveform_mul_self`: a waveform against itself
  averages to `V.re^2 + V.im^2`.
- `average_rmsWaveform_mul_quadrature`: a quadrature waveform
  averages to `0`.
- `average_peakWaveform_mul_peakWaveform`: the peak-waveform
  average is `(1/2) * Re(V * conj I)`.

## iii. Table of contents

- A. RMS and peak waveform averages

## iv. References

- J. W. Nilsson and S. A. Riedel, *Electric Circuits*, eleventh
  edition, Pearson, 2019: sinusoidal steady-state average power
  and the RMS phasor convention.

## A. RMS and peak waveform averages
-/

@[expose] public section

namespace PhyslibExt.Circuits.RMSAveragePower

/-- The peak phasor waveform `Re (V * exp (i * ω * t))`: the leaf RMS
formula with the `sqrt(2)` factor omitted. -/
noncomputable def peakWaveform (V : ℂ) (ω t : ℝ) : ℝ :=
  (V * Complex.exp (↑(ω * t) * Complex.I)).re

/-- The RMS phasor waveform `sqrt(2) * Re (V * exp (i * ω * t))`. -/
noncomputable def rmsWaveform (V : ℂ) (ω t : ℝ) : ℝ :=
  Real.sqrt 2 * (V * Complex.exp (↑(ω * t) * Complex.I)).re

private theorem re_mul_conj (V I : ℂ) :
    (V * starRingEnd ℂ I).re = V.re * I.re + V.im * I.im := by
  have h1 : (starRingEnd ℂ I).re = I.re := by simp
  have h2 : (starRingEnd ℂ I).im = -I.im := by simp
  rw [Complex.mul_re, h1, h2]
  ring

private theorem cos_sq_period (ω a : ℝ) (hω : 0 < ω) :
    (∫ t in a..(a + 2 * Real.pi / ω), Real.cos (ω * t) ^ 2) = Real.pi / ω := by
  have hω' : ω ≠ 0 := ne_of_gt hω
  have hper : ω * (a + 2 * Real.pi / ω) = ω * a + 2 * Real.pi := by
    have h1 : ω * (2 * Real.pi / ω) = 2 * Real.pi := by
      rw [← mul_div_assoc, div_eq_iff hω']
      ring
    rw [mul_add, h1]
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.cos x ^ 2) hω', hper]
  simp only [integral_cos_sq, Real.cos_add_two_pi, Real.sin_add_two_pi, smul_eq_mul]
  field_simp [hω']
  ring

private theorem sin_sq_period (ω a : ℝ) (hω : 0 < ω) :
    (∫ t in a..(a + 2 * Real.pi / ω), Real.sin (ω * t) ^ 2) = Real.pi / ω := by
  have hω' : ω ≠ 0 := ne_of_gt hω
  have hper : ω * (a + 2 * Real.pi / ω) = ω * a + 2 * Real.pi := by
    have h1 : ω * (2 * Real.pi / ω) = 2 * Real.pi := by
      rw [← mul_div_assoc, div_eq_iff hω']
      ring
    rw [mul_add, h1]
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x ^ 2) hω', hper]
  simp only [integral_sin_sq, Real.sin_add_two_pi, Real.cos_add_two_pi, smul_eq_mul]
  field_simp [hω']
  ring

private theorem sin_mul_cos_period (ω a : ℝ) (hω : 0 < ω) :
    (∫ t in a..(a + 2 * Real.pi / ω), Real.sin (ω * t) * Real.cos (ω * t)) = 0 := by
  have hω' : ω ≠ 0 := ne_of_gt hω
  have hper : ω * (a + 2 * Real.pi / ω) = ω * a + 2 * Real.pi := by
    have h1 : ω * (2 * Real.pi / ω) = 2 * Real.pi := by
      rw [← mul_div_assoc, div_eq_iff hω']
      ring
    rw [mul_add, h1]
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x * Real.cos x) hω',
    hper]
  simp only [integral_sin_mul_cos₁, Real.sin_add_two_pi, smul_eq_mul]
  field_simp [hω']
  ring

/-- At time zero the peak waveform is the real part of the phasor. -/
lemma peakWaveform_at_zero (V : ℂ) (ω : ℝ) :
    peakWaveform V ω 0 = V.re := by
  simp [peakWaveform]

/-- At time zero the RMS waveform is `sqrt(2)` times the real part of
the phasor. -/
lemma rmsWaveform_at_zero (V : ℂ) (ω : ℝ) :
    rmsWaveform V ω 0 = Real.sqrt 2 * V.re := by
  simp [rmsWaveform]

/-- The RMS waveform is `sqrt(2)` times the peak waveform, pointwise. -/
lemma rmsWaveform_eq_sqrt_two_mul_peakWaveform (V : ℂ) (ω t : ℝ) :
    rmsWaveform V ω t = Real.sqrt 2 * peakWaveform V ω t := by
  rfl

/-- Pointwise expansion of the product of two RMS waveforms in the
`cos (ω * t) ^ 2`, `sin (ω * t) ^ 2`, `sin (ω * t) * cos (ω * t)`
basis supported by Mathlib's endpoint integral lemmas
`integral_cos_sq`, `integral_sin_sq`, and `integral_sin_mul_cos₁`
after scaling the argument by `ω`. -/
lemma rmsWaveform_mul_rmsWaveform_expansion (V I : ℂ) (ω t : ℝ) :
    rmsWaveform V ω t * rmsWaveform I ω t
      = 2 * (V.re * I.re * Real.cos (ω * t) ^ 2
          + V.im * I.im * Real.sin (ω * t) ^ 2
          - (V.re * I.im + V.im * I.re)
            * (Real.sin (ω * t) * Real.cos (ω * t))) := by
  have hV : (V * Complex.exp (↑(ω * t) * Complex.I)).re
      = V.re * Real.cos (ω * t) - V.im * Real.sin (ω * t) := by
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hI : (I * Complex.exp (↑(ω * t) * Complex.I)).re
      = I.re * Real.cos (ω * t) - I.im * Real.sin (ω * t) := by
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hfactor : (Real.sqrt 2 * (V.re * Real.cos (ω * t) - V.im * Real.sin (ω * t)))
        * (Real.sqrt 2 * (I.re * Real.cos (ω * t) - I.im * Real.sin (ω * t)))
      = (Real.sqrt 2 * Real.sqrt 2)
        * ((V.re * Real.cos (ω * t) - V.im * Real.sin (ω * t))
          * (I.re * Real.cos (ω * t) - I.im * Real.sin (ω * t))) := by ring
  simp only [rmsWaveform, hV, hI]
  rw [hfactor, hsq]
  ring

/-- The integral of the product of two RMS waveforms over any complete
period `2 * π / ω`, starting at an arbitrary `a`, is the period times
`Re (V * conj I)`. -/
lemma integral_rmsWaveform_mul_rmsWaveform_over_period
    (V I : ℂ) {ω : ℝ} (hω : 0 < ω) (a : ℝ) :
    (∫ t in a..(a + 2 * Real.pi / ω),
      rmsWaveform V ω t * rmsWaveform I ω t)
      = (2 * Real.pi / ω) * (V * starRingEnd ℂ I).re := by
  have hω' : ω ≠ 0 := ne_of_gt hω
  have hcos : Continuous (fun t : ℝ => Real.cos (ω * t)) :=
    Real.continuous_cos.comp (Continuous.mul continuous_const continuous_id)
  have hsin : Continuous (fun t : ℝ => Real.sin (ω * t)) :=
    Real.continuous_sin.comp (Continuous.mul continuous_const continuous_id)
  have hcA : Continuous (fun t : ℝ => V.re * I.re * Real.cos (ω * t) ^ 2) :=
    Continuous.mul continuous_const (hcos.pow 2)
  have hcB : Continuous (fun t : ℝ => V.im * I.im * Real.sin (ω * t) ^ 2) :=
    Continuous.mul continuous_const (hsin.pow 2)
  have hcC : Continuous (fun t : ℝ => (V.re * I.im + V.im * I.re)
      * (Real.sin (ω * t) * Real.cos (ω * t))) :=
    Continuous.mul continuous_const (Continuous.mul hsin hcos)
  have hcAB : Continuous (fun t : ℝ => V.re * I.re * Real.cos (ω * t) ^ 2
      + V.im * I.im * Real.sin (ω * t) ^ 2) :=
    hcA.add hcB
  have hA : IntervalIntegrable (fun t : ℝ => V.re * I.re * Real.cos (ω * t) ^ 2)
      MeasureTheory.volume a (a + 2 * Real.pi / ω) := hcA.intervalIntegrable a (a + 2 * Real.pi / ω)
  have hB : IntervalIntegrable (fun t : ℝ => V.im * I.im * Real.sin (ω * t) ^ 2)
      MeasureTheory.volume a (a + 2 * Real.pi / ω) := hcB.intervalIntegrable a (a + 2 * Real.pi / ω)
  have hC : IntervalIntegrable (fun t : ℝ => (V.re * I.im + V.im * I.re)
      * (Real.sin (ω * t) * Real.cos (ω * t)))
      MeasureTheory.volume a (a + 2 * Real.pi / ω) := hcC.intervalIntegrable a (a + 2 * Real.pi / ω)
  have hAB : IntervalIntegrable (fun t : ℝ => V.re * I.re * Real.cos (ω * t) ^ 2
      + V.im * I.im * Real.sin (ω * t) ^ 2)
      MeasureTheory.volume a (a + 2 * Real.pi / ω) := hcAB.intervalIntegrable a (a + 2 * Real.pi / ω)
  simp only [rmsWaveform_mul_rmsWaveform_expansion]
  have h2 : (∫ t in a..(a + 2 * Real.pi / ω),
        2 * (V.re * I.re * Real.cos (ω * t) ^ 2 + V.im * I.im * Real.sin (ω * t) ^ 2
          - (V.re * I.im + V.im * I.re) * (Real.sin (ω * t) * Real.cos (ω * t))))
      = 2 * (∫ t in a..(a + 2 * Real.pi / ω),
        (V.re * I.re * Real.cos (ω * t) ^ 2 + V.im * I.im * Real.sin (ω * t) ^ 2
          - (V.re * I.im + V.im * I.re) * (Real.sin (ω * t) * Real.cos (ω * t)))) :=
    intervalIntegral.integral_const_mul _ _
  rw [h2]
  have hSub : (∫ t in a..(a + 2 * Real.pi / ω),
        (V.re * I.re * Real.cos (ω * t) ^ 2 + V.im * I.im * Real.sin (ω * t) ^ 2
          - (V.re * I.im + V.im * I.re) * (Real.sin (ω * t) * Real.cos (ω * t))))
      = (∫ t in a..(a + 2 * Real.pi / ω),
        (V.re * I.re * Real.cos (ω * t) ^ 2 + V.im * I.im * Real.sin (ω * t) ^ 2))
        - (∫ t in a..(a + 2 * Real.pi / ω),
        (V.re * I.im + V.im * I.re) * (Real.sin (ω * t) * Real.cos (ω * t))) :=
    intervalIntegral.integral_sub hAB hC
  rw [hSub]
  have hAdd : (∫ t in a..(a + 2 * Real.pi / ω),
        (V.re * I.re * Real.cos (ω * t) ^ 2 + V.im * I.im * Real.sin (ω * t) ^ 2))
      = (∫ t in a..(a + 2 * Real.pi / ω), V.re * I.re * Real.cos (ω * t) ^ 2)
        + (∫ t in a..(a + 2 * Real.pi / ω), V.im * I.im * Real.sin (ω * t) ^ 2) :=
    intervalIntegral.integral_add hA hB
  rw [hAdd]
  have hAout : (∫ t in a..(a + 2 * Real.pi / ω), V.re * I.re * Real.cos (ω * t) ^ 2)
      = V.re * I.re * (Real.pi / ω) := by
    have hcongr : (∫ t in a..(a + 2 * Real.pi / ω), V.re * I.re * Real.cos (ω * t) ^ 2)
        = V.re * I.re * (∫ t in a..(a + 2 * Real.pi / ω), Real.cos (ω * t) ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    rw [hcongr, cos_sq_period ω a hω]
  have hBout : (∫ t in a..(a + 2 * Real.pi / ω), V.im * I.im * Real.sin (ω * t) ^ 2)
      = V.im * I.im * (Real.pi / ω) := by
    have hcongr : (∫ t in a..(a + 2 * Real.pi / ω), V.im * I.im * Real.sin (ω * t) ^ 2)
        = V.im * I.im * (∫ t in a..(a + 2 * Real.pi / ω), Real.sin (ω * t) ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    rw [hcongr, sin_sq_period ω a hω]
  have hCout : (∫ t in a..(a + 2 * Real.pi / ω),
        (V.re * I.im + V.im * I.re) * (Real.sin (ω * t) * Real.cos (ω * t)))
      = (V.re * I.im + V.im * I.re) * 0 := by
    have hcongr : (∫ t in a..(a + 2 * Real.pi / ω),
          (V.re * I.im + V.im * I.re) * (Real.sin (ω * t) * Real.cos (ω * t)))
        = (V.re * I.im + V.im * I.re)
          * (∫ t in a..(a + 2 * Real.pi / ω), Real.sin (ω * t) * Real.cos (ω * t)) :=
      intervalIntegral.integral_const_mul _ _
    rw [hcongr, sin_mul_cos_period ω a hω]
  rw [hAout, hBout, hCout, re_mul_conj]
  field_simp [hω']
  ring

/-- Headline result: the average of `v * i` over any complete period
`2 * π / ω`, for RMS phasors `v` and `i` sharing the frequency `ω` and
the `exp (+i * ω * t)` convention, is `Re (V * conj I)`. -/
lemma average_rmsWaveform_mul_rmsWaveform
    (V I : ℂ) {ω : ℝ} (hω : 0 < ω) (a : ℝ) :
    (∫ t in a..(a + 2 * Real.pi / ω),
      rmsWaveform V ω t * rmsWaveform I ω t) / (2 * Real.pi / ω)
      = (V * starRingEnd ℂ I).re := by
  have h := integral_rmsWaveform_mul_rmsWaveform_over_period V I hω a
  have hω' : ω ≠ 0 := ne_of_gt hω
  have hT : (2 * Real.pi / ω) ≠ 0 := by
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have h2pi : (2:ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) hpi
    exact div_ne_zero h2pi hω'
  rw [h]
  field_simp [hT]

/-- In-phase validation case: a waveform averaged against itself
gives the canonical norm square `Complex.normSq V`, i.e.
`Re (V * conj V)`. -/
lemma average_rmsWaveform_mul_self
    (V : ℂ) {ω : ℝ} (hω : 0 < ω) (a : ℝ) :
    (∫ t in a..(a + 2 * Real.pi / ω),
      rmsWaveform V ω t * rmsWaveform V ω t) / (2 * Real.pi / ω)
      = Complex.normSq V := by
  have h := average_rmsWaveform_mul_rmsWaveform V V hω a
  rw [h, re_mul_conj, Complex.normSq_apply]

/-- The in-phase average in coordinates: `V.re ^ 2 + V.im ^ 2`. -/
lemma average_rmsWaveform_mul_self_re_im
    (V : ℂ) {ω : ℝ} (hω : 0 < ω) (a : ℝ) :
    (∫ t in a..(a + 2 * Real.pi / ω),
      rmsWaveform V ω t * rmsWaveform V ω t) / (2 * Real.pi / ω)
      = V.re ^ 2 + V.im ^ 2 := by
  have h := average_rmsWaveform_mul_self V hω a
  rw [h, Complex.normSq_apply]
  ring

/-- Quadrature validation case: a waveform averaged against the
waveform of the phasor rotated by `i` gives zero. -/
lemma average_rmsWaveform_mul_quadrature
    (V : ℂ) {ω : ℝ} (hω : 0 < ω) (a : ℝ) :
    (∫ t in a..(a + 2 * Real.pi / ω),
      rmsWaveform V ω t * rmsWaveform (Complex.I * V) ω t)
        / (2 * Real.pi / ω)
      = 0 := by
  have h := average_rmsWaveform_mul_rmsWaveform V (Complex.I * V) hω a
  have hIVre : (Complex.I * V).re = -V.im := by simp [Complex.mul_re]
  have hIVim : (Complex.I * V).im = V.re := by simp [Complex.mul_im]
  rw [h, re_mul_conj, hIVre, hIVim]
  ring

/-- The integral of the product of two peak waveforms over any
complete period `2 * π / ω`, starting at an arbitrary `a`, is the
period times `(1 / 2) * Re (V * conj I)`. -/
lemma integral_peakWaveform_mul_peakWaveform_over_period
    (V I : ℂ) {ω : ℝ} (hω : 0 < ω) (a : ℝ) :
    (∫ t in a..(a + 2 * Real.pi / ω),
      peakWaveform V ω t * peakWaveform I ω t)
      = (2 * Real.pi / ω) * ((1 / 2) * (V * starRingEnd ℂ I).re) := by
  have h := integral_rmsWaveform_mul_rmsWaveform_over_period V I hω a
  have hω' : ω ≠ 0 := ne_of_gt hω
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hrel : ∀ t : ℝ, peakWaveform V ω t * peakWaveform I ω t
      = (1 / 2) * (rmsWaveform V ω t * rmsWaveform I ω t) := by
    intro t
    have h3 : (Real.sqrt 2 * peakWaveform V ω t) * (Real.sqrt 2 * peakWaveform I ω t)
        = (Real.sqrt 2 * Real.sqrt 2) * (peakWaveform V ω t * peakWaveform I ω t) := by
      ring
    rw [rmsWaveform_eq_sqrt_two_mul_peakWaveform, rmsWaveform_eq_sqrt_two_mul_peakWaveform,
      h3, hsq]
    ring
  have hmain : (∫ t in a..(a + 2 * Real.pi / ω), peakWaveform V ω t * peakWaveform I ω t)
      = (1 / 2) * (∫ t in a..(a + 2 * Real.pi / ω),
        rmsWaveform V ω t * rmsWaveform I ω t) := by
    simp only [hrel, intervalIntegral.integral_const_mul]
  rw [hmain, h]
  field_simp [hω']

/-- Peak-phasor convention: omitting the `sqrt(2)` RMS factor, the
average of the product over any complete period has the factor
`1 / 2`, not the RMS formula. -/
lemma average_peakWaveform_mul_peakWaveform
    (V I : ℂ) {ω : ℝ} (hω : 0 < ω) (a : ℝ) :
    (∫ t in a..(a + 2 * Real.pi / ω),
      peakWaveform V ω t * peakWaveform I ω t) / (2 * Real.pi / ω)
      = (1 / 2) * (V * starRingEnd ℂ I).re := by
  have h := integral_peakWaveform_mul_peakWaveform_over_period V I hω a
  have hω' : ω ≠ 0 := ne_of_gt hω
  have hT : (2 * Real.pi / ω) ≠ 0 := by
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have h2pi : (2:ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) hpi
    exact div_ne_zero h2pi hω'
  rw [h]
  field_simp [hT]

end PhyslibExt.Circuits.RMSAveragePower
