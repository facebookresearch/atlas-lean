/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import PhyslibExt.Circuits.RMSAveragePower

/-!
# Finite in-phase and quadrature signal space

## i. Overview

For a real observation length `T > 0` and an integer carrier index
`k >= 1`, the in-phase waveform `sqrt(2/T) * cos(2 * pi * k * t / T)`
and the quadrature waveform `-sqrt(2/T) * sin(2 * pi * k * t / T)` on
`[0, T]` form an orthonormal pair under the real inner product given
by integration over `[0, T]`. A constant-coefficient waveform
`a * u + b * v` built from them has energy `a^2 + b^2`, and its inner
products against `u` and `v` recover the coefficients `a` and `b`.
The coefficients are constant on the interval; no time-varying
envelope is treated as a constant. This is the two-dimensional real
signal-space representation of a bandpass signal in terms of its
in-phase and quadrature components. With angular frequency
`omega = 2 * pi * k / T`, the in-phase, quadrature and combined
waveforms are the root-mean-square phasor waveforms
`rmsWaveform` of `PhyslibExt.Circuits.RMSAveragePower` with phasors
`sqrt(1/T)`, `i * sqrt(1/T)` and `(a + b * i) * sqrt(1/T)`; public
bridge lemmas state these identities, so results about `rmsWaveform`
rewrite to this API. In that file,
`average_rmsWaveform_mul_rmsWaveform` gives a period average of
`Re (V * conj I)` for root-mean-square waveforms, while
`average_peakWaveform_mul_peakWaveform` gives half that value for
peak waveforms. The proofs here rescale the carrier argument and use
the Mathlib interval integrals `integral_cos_sq`, `integral_sin_sq`
and `integral_sin_mul_cos₁` over a full period, where the endpoint
sine terms vanish because `k` is an integer.

## ii. Key results

- `inPhaseWaveform_norm` and `quadratureWaveform_norm`: each
  waveform has unit energy on `[0, T]`.
- `inPhaseWaveform_quadratureWaveform_orthogonal`: the two
  waveforms are orthogonal on `[0, T]`.
- `iqWaveform_energy`: the energy of `a * u + b * v` is
  `a^2 + b^2`.
- `iqWaveform_projection_inPhase` and
  `iqWaveform_projection_quadrature`: projecting the combined
  waveform against `u` and `v` recovers `a` and `b`.
- `iqBasis_orthonormal_energy_and_projection`: the combined
  orthonormality, energy and projection statement.
- `inPhaseWaveform_eq_rmsWaveform`,
  `quadratureWaveform_eq_rmsWaveform` and
  `iqWaveform_eq_rmsWaveform`: the three waveforms as
  root-mean-square phasor waveforms.

## iii. Table of contents

- A. In-phase, quadrature and combined waveforms
- B. Orthonormality on the observation interval
- C. Energy and coefficient recovery
- D. Concrete validations and carrier mismatch

## iv. References

- J. G. Proakis and M. Salehi, *Communication Systems Engineering*,
  second edition, Prentice Hall, 2002: the signal-space
  representation of bandpass signals by in-phase and quadrature
  components on an orthonormal basis.

## A. In-phase, quadrature and combined waveforms
-/

@[expose] public section

namespace PhyslibExt.Communications.FiniteIQSignalSpace

/-- The in-phase waveform `sqrt(2/T) * cos(2 * pi * k * t / T)`. -/
noncomputable def inPhaseWaveform (T : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (2 / T) * Real.cos (2 * Real.pi * (k : ℝ) * t / T)

/-- The quadrature waveform `-sqrt(2/T) * sin(2 * pi * k * t / T)`. -/
noncomputable def quadratureWaveform (T : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  -Real.sqrt (2 / T) * Real.sin (2 * Real.pi * (k : ℝ) * t / T)

/-- The constant-coefficient waveform `a * u + b * v`. -/
noncomputable def iqWaveform (a b T : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  a * inPhaseWaveform T k t + b * quadratureWaveform T k t

private lemma sqrt_two_div_eq (T : ℝ) :
    Real.sqrt (2 / T) = Real.sqrt 2 * Real.sqrt (1 / T) := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_one_div]

/-- The in-phase waveform is the root-mean-square phasor waveform of
the real phasor `sqrt(1/T)` at angular frequency `2 * pi * k / T`. -/
theorem inPhaseWaveform_eq_rmsWaveform (T : ℝ) (k : ℕ) (t : ℝ) :
    inPhaseWaveform T k t
      = PhyslibExt.Circuits.RMSAveragePower.rmsWaveform
          (Real.sqrt (1 / T) : ℂ) (2 * Real.pi * (k : ℝ) / T) t := by
  have harg : 2 * Real.pi * (k : ℝ) / T * t = 2 * Real.pi * (k : ℝ) * t / T := by ring
  unfold inPhaseWaveform PhyslibExt.Circuits.RMSAveragePower.rmsWaveform
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, harg, sqrt_two_div_eq]
  ring

/-- The quadrature waveform is the root-mean-square phasor waveform of
the phasor `i * sqrt(1/T)` at angular frequency `2 * pi * k / T`. -/
theorem quadratureWaveform_eq_rmsWaveform (T : ℝ) (k : ℕ) (t : ℝ) :
    quadratureWaveform T k t
      = PhyslibExt.Circuits.RMSAveragePower.rmsWaveform
          (Complex.I * (Real.sqrt (1 / T) : ℂ)) (2 * Real.pi * (k : ℝ) / T) t := by
  have harg : 2 * Real.pi * (k : ℝ) / T * t = 2 * Real.pi * (k : ℝ) * t / T := by ring
  have hre : (Complex.I * (Real.sqrt (1 / T) : ℂ)).re = 0 := by simp
  have him : (Complex.I * (Real.sqrt (1 / T) : ℂ)).im = Real.sqrt (1 / T) := by simp
  unfold quadratureWaveform PhyslibExt.Circuits.RMSAveragePower.rmsWaveform
  rw [Complex.mul_re, hre, him, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    harg, sqrt_two_div_eq]
  ring

/-- The combined waveform `a * u + b * v` is the root-mean-square
phasor waveform of the phasor `(a + b * i) * sqrt(1/T)` at angular
frequency `2 * pi * k / T`. -/
theorem iqWaveform_eq_rmsWaveform (a b T : ℝ) (k : ℕ) (t : ℝ) :
    iqWaveform a b T k t
      = PhyslibExt.Circuits.RMSAveragePower.rmsWaveform
          (((a : ℂ) + (b : ℂ) * Complex.I) * (Real.sqrt (1 / T) : ℂ))
          (2 * Real.pi * (k : ℝ) / T) t := by
  have harg : 2 * Real.pi * (k : ℝ) / T * t = 2 * Real.pi * (k : ℝ) * t / T := by ring
  have hre : (((a : ℂ) + (b : ℂ) * Complex.I) * (Real.sqrt (1 / T) : ℂ)).re
      = a * Real.sqrt (1 / T) := by simp [Complex.mul_re]
  have him : (((a : ℂ) + (b : ℂ) * Complex.I) * (Real.sqrt (1 / T) : ℂ)).im
      = b * Real.sqrt (1 / T) := by simp [Complex.mul_im]
  unfold iqWaveform inPhaseWaveform quadratureWaveform
    PhyslibExt.Circuits.RMSAveragePower.rmsWaveform
  rw [Complex.mul_re, hre, him, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    harg, sqrt_two_div_eq]
  ring

/-! ## B. Orthonormality on the observation interval -/

private lemma sin_two_pi_mul_cast (k : ℕ) : Real.sin (2 * Real.pi * (k : ℝ)) = 0 := by
  have h0 : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    have h := Real.sin_add_nat_mul_two_pi (0 : ℝ) k
    simpa using h
  have harg : (2 : ℝ) * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) := by ring
  rw [harg]
  exact h0

private lemma cos_sq_scaled_integral (T : ℝ) (k : ℕ) (hT : 0 < T) (hk : 1 ≤ k) :
    (∫ t in (0 : ℝ)..T, Real.cos (2 * Real.pi * (k : ℝ) * t / T) ^ 2) = T / 2 := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hkpos : 0 < k := by omega
  have hkRpos : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hkRne : (k : ℝ) ≠ 0 := ne_of_gt hkRpos
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcpos : 0 < 2 * Real.pi * (k : ℝ) / T := by positivity
  have hcne : (2 * Real.pi * (k : ℝ) / T) ≠ 0 := ne_of_gt hcpos
  have hrewrite : (∫ t in (0 : ℝ)..T, Real.cos (2 * Real.pi * (k : ℝ) * t / T) ^ 2)
      = ∫ t in (0 : ℝ)..T, (fun u : ℝ => Real.cos u ^ 2) ((2 * Real.pi * (k : ℝ) / T) * t) := by
    apply intervalIntegral.integral_congr
    intro x _
    have harg : (2 : ℝ) * Real.pi * (k : ℝ) * x / T = (2 * Real.pi * (k : ℝ) / T) * x := by
      ring
    change Real.cos (2 * Real.pi * (k : ℝ) * x / T) ^ 2
      = (fun u : ℝ => Real.cos u ^ 2) ((2 * Real.pi * (k : ℝ) / T) * x)
    rw [harg]
  rw [hrewrite]
  have hcomp := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := T)
    (fun u : ℝ => Real.cos u ^ 2) hcne
  rw [hcomp]
  simp only [smul_eq_mul]
  have hc0 : (2 * Real.pi * (k : ℝ) / T) * 0 = 0 := by ring
  have hcT : (2 * Real.pi * (k : ℝ) / T) * T = 2 * Real.pi * (k : ℝ) := by
    field_simp
  rw [hc0, hcT]
  rw [integral_cos_sq]
  have hsin : Real.sin (2 * Real.pi * (k : ℝ)) = 0 := sin_two_pi_mul_cast k
  simp [hsin]
  field_simp

private lemma sin_sq_scaled_integral (T : ℝ) (k : ℕ) (hT : 0 < T) (hk : 1 ≤ k) :
    (∫ t in (0 : ℝ)..T, Real.sin (2 * Real.pi * (k : ℝ) * t / T) ^ 2) = T / 2 := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hkpos : 0 < k := by omega
  have hkRpos : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hkRne : (k : ℝ) ≠ 0 := ne_of_gt hkRpos
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcpos : 0 < 2 * Real.pi * (k : ℝ) / T := by positivity
  have hcne : (2 * Real.pi * (k : ℝ) / T) ≠ 0 := ne_of_gt hcpos
  have hrewrite : (∫ t in (0 : ℝ)..T, Real.sin (2 * Real.pi * (k : ℝ) * t / T) ^ 2)
      = ∫ t in (0 : ℝ)..T, (fun u : ℝ => Real.sin u ^ 2) ((2 * Real.pi * (k : ℝ) / T) * t) := by
    apply intervalIntegral.integral_congr
    intro x _
    have harg : (2 : ℝ) * Real.pi * (k : ℝ) * x / T = (2 * Real.pi * (k : ℝ) / T) * x := by
      ring
    change Real.sin (2 * Real.pi * (k : ℝ) * x / T) ^ 2
      = (fun u : ℝ => Real.sin u ^ 2) ((2 * Real.pi * (k : ℝ) / T) * x)
    rw [harg]
  rw [hrewrite]
  have hcomp := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := T)
    (fun u : ℝ => Real.sin u ^ 2) hcne
  rw [hcomp]
  simp only [smul_eq_mul]
  have hc0 : (2 * Real.pi * (k : ℝ) / T) * 0 = 0 := by ring
  have hcT : (2 * Real.pi * (k : ℝ) / T) * T = 2 * Real.pi * (k : ℝ) := by
    field_simp
  rw [hc0, hcT]
  rw [integral_sin_sq]
  have hsin : Real.sin (2 * Real.pi * (k : ℝ)) = 0 := sin_two_pi_mul_cast k
  simp [hsin]
  field_simp

private lemma sin_cos_scaled_integral (T : ℝ) (k : ℕ) (hT : 0 < T) (hk : 1 ≤ k) :
    (∫ t in (0 : ℝ)..T, Real.sin (2 * Real.pi * (k : ℝ) * t / T)
      * Real.cos (2 * Real.pi * (k : ℝ) * t / T)) = 0 := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hkpos : 0 < k := by omega
  have hkRpos : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hcpos : 0 < 2 * Real.pi * (k : ℝ) / T := by positivity
  have hcne : (2 * Real.pi * (k : ℝ) / T) ≠ 0 := ne_of_gt hcpos
  have hrewrite : (∫ t in (0 : ℝ)..T, Real.sin (2 * Real.pi * (k : ℝ) * t / T)
        * Real.cos (2 * Real.pi * (k : ℝ) * t / T))
      = ∫ t in (0 : ℝ)..T, (fun u : ℝ => Real.sin u * Real.cos u)
          ((2 * Real.pi * (k : ℝ) / T) * t) := by
    apply intervalIntegral.integral_congr
    intro x _
    have harg : (2 : ℝ) * Real.pi * (k : ℝ) * x / T = (2 * Real.pi * (k : ℝ) / T) * x := by
      ring
    change Real.sin (2 * Real.pi * (k : ℝ) * x / T)
            * Real.cos (2 * Real.pi * (k : ℝ) * x / T)
      = (fun u : ℝ => Real.sin u * Real.cos u) ((2 * Real.pi * (k : ℝ) / T) * x)
    rw [harg]
  rw [hrewrite]
  have hcomp := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := T)
    (fun u : ℝ => Real.sin u * Real.cos u) hcne
  rw [hcomp]
  simp only [smul_eq_mul]
  have hc0 : (2 * Real.pi * (k : ℝ) / T) * 0 = 0 := by ring
  have hcT : (2 * Real.pi * (k : ℝ) / T) * T = 2 * Real.pi * (k : ℝ) := by
    field_simp
  rw [hc0, hcT]
  rw [integral_sin_mul_cos₁]
  have hsin : Real.sin (2 * Real.pi * (k : ℝ)) = 0 := sin_two_pi_mul_cast k
  simp [hsin]

/-- The in-phase waveform has unit energy on `[0, T]`. -/
theorem inPhaseWaveform_norm (T : ℝ) (k : ℕ) (hT : 0 < T) (hk : 1 ≤ k) :
    (∫ t in (0 : ℝ)..T, inPhaseWaveform T k t * inPhaseWaveform T k t) = 1 := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have h2T : 0 ≤ (2 : ℝ) / T := by positivity
  have hsq : Real.sqrt (2 / T) * Real.sqrt (2 / T) = 2 / T :=
    Real.mul_self_sqrt h2T
  have hrewrite : (∫ t in (0 : ℝ)..T, inPhaseWaveform T k t * inPhaseWaveform T k t)
      = ∫ t in (0 : ℝ)..T, (2 / T) * (Real.cos (2 * Real.pi * (k : ℝ) * t / T) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x _
    change inPhaseWaveform T k x * inPhaseWaveform T k x = _
    unfold inPhaseWaveform
    have hpow : Real.cos (2 * Real.pi * (k : ℝ) * x / T)
            * Real.cos (2 * Real.pi * (k : ℝ) * x / T)
        = Real.cos (2 * Real.pi * (k : ℝ) * x / T) ^ 2 := by ring
    calc Real.sqrt (2 / T) * Real.cos (2 * Real.pi * (k : ℝ) * x / T) *
        (Real.sqrt (2 / T) * Real.cos (2 * Real.pi * (k : ℝ) * x / T))
        = (Real.sqrt (2 / T) * Real.sqrt (2 / T)) *
          (Real.cos (2 * Real.pi * (k : ℝ) * x / T)
            * Real.cos (2 * Real.pi * (k : ℝ) * x / T)) := by ring
      _ = (2 / T) * (Real.cos (2 * Real.pi * (k : ℝ) * x / T)
            * Real.cos (2 * Real.pi * (k : ℝ) * x / T)) := by rw [hsq]
      _ = (2 / T) * (Real.cos (2 * Real.pi * (k : ℝ) * x / T) ^ 2) := by rw [hpow]
  rw [hrewrite, intervalIntegral.integral_const_mul, cos_sq_scaled_integral T k hT hk]
  field_simp

/-- The quadrature waveform has unit energy on `[0, T]`. -/
theorem quadratureWaveform_norm (T : ℝ) (k : ℕ) (hT : 0 < T) (hk : 1 ≤ k) :
    (∫ t in (0 : ℝ)..T, quadratureWaveform T k t * quadratureWaveform T k t) = 1 := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have h2T : 0 ≤ (2 : ℝ) / T := by positivity
  have hsq : Real.sqrt (2 / T) * Real.sqrt (2 / T) = 2 / T :=
    Real.mul_self_sqrt h2T
  have hrewrite : (∫ t in (0 : ℝ)..T, quadratureWaveform T k t * quadratureWaveform T k t)
      = ∫ t in (0 : ℝ)..T, (2 / T) * (Real.sin (2 * Real.pi * (k : ℝ) * t / T) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x _
    change quadratureWaveform T k x * quadratureWaveform T k x = _
    unfold quadratureWaveform
    have hpow : Real.sin (2 * Real.pi * (k : ℝ) * x / T)
            * Real.sin (2 * Real.pi * (k : ℝ) * x / T)
        = Real.sin (2 * Real.pi * (k : ℝ) * x / T) ^ 2 := by ring
    calc (-Real.sqrt (2 / T)) * Real.sin (2 * Real.pi * (k : ℝ) * x / T) *
        ((-Real.sqrt (2 / T)) * Real.sin (2 * Real.pi * (k : ℝ) * x / T))
        = (Real.sqrt (2 / T) * Real.sqrt (2 / T)) *
          (Real.sin (2 * Real.pi * (k : ℝ) * x / T)
            * Real.sin (2 * Real.pi * (k : ℝ) * x / T)) := by ring
      _ = (2 / T) * (Real.sin (2 * Real.pi * (k : ℝ) * x / T)
            * Real.sin (2 * Real.pi * (k : ℝ) * x / T)) := by rw [hsq]
      _ = (2 / T) * (Real.sin (2 * Real.pi * (k : ℝ) * x / T) ^ 2) := by rw [hpow]
  rw [hrewrite, intervalIntegral.integral_const_mul, sin_sq_scaled_integral T k hT hk]
  field_simp

/-- The in-phase and quadrature waveforms are orthogonal on `[0, T]`. -/
theorem inPhaseWaveform_quadratureWaveform_orthogonal (T : ℝ) (k : ℕ)
    (hT : 0 < T) (hk : 1 ≤ k) :
    (∫ t in (0 : ℝ)..T, inPhaseWaveform T k t * quadratureWaveform T k t) = 0 := by
  have h2T : 0 ≤ (2 : ℝ) / T := by positivity
  have hsq : Real.sqrt (2 / T) * Real.sqrt (2 / T) = 2 / T :=
    Real.mul_self_sqrt h2T
  have hrewrite : (∫ t in (0 : ℝ)..T, inPhaseWaveform T k t * quadratureWaveform T k t)
      = ∫ t in (0 : ℝ)..T, (-(2 / T)) * (Real.sin (2 * Real.pi * (k : ℝ) * t / T)
          * Real.cos (2 * Real.pi * (k : ℝ) * t / T)) := by
    apply intervalIntegral.integral_congr
    intro x _
    change inPhaseWaveform T k x * quadratureWaveform T k x = _
    unfold inPhaseWaveform quadratureWaveform
    have hring : (Real.sqrt (2 / T) * Real.cos (2 * Real.pi * (k : ℝ) * x / T)) *
        ((-Real.sqrt (2 / T)) * Real.sin (2 * Real.pi * (k : ℝ) * x / T))
        = (-(Real.sqrt (2 / T) * Real.sqrt (2 / T))) *
          (Real.sin (2 * Real.pi * (k : ℝ) * x / T)
            * Real.cos (2 * Real.pi * (k : ℝ) * x / T)) := by ring
    rw [hring, hsq]
  rw [hrewrite, intervalIntegral.integral_const_mul, sin_cos_scaled_integral T k hT hk]
  ring

/-! ## C. Energy and coefficient recovery -/

/-- The energy of `a * u + b * v` on `[0, T]` is `a^2 + b^2`. -/
theorem iqWaveform_energy (a b T : ℝ) (k : ℕ) (hT : 0 < T) (hk : 1 ≤ k) :
    (∫ t in (0 : ℝ)..T, iqWaveform a b T k t * iqWaveform a b T k t)
      = a ^ 2 + b ^ 2 := by
  have hU : Continuous (fun t : ℝ => inPhaseWaveform T k t) := by
    unfold inPhaseWaveform
    fun_prop
  have hV : Continuous (fun t : ℝ => quadratureWaveform T k t) := by
    unfold quadratureWaveform
    fun_prop
  have hUU : IntervalIntegrable (fun t : ℝ => inPhaseWaveform T k t * inPhaseWaveform T k t)
      MeasureTheory.volume 0 T :=
    (hU.mul hU).intervalIntegrable 0 T
  have hVV : IntervalIntegrable (fun t : ℝ => quadratureWaveform T k t * quadratureWaveform T k t)
      MeasureTheory.volume 0 T :=
    (hV.mul hV).intervalIntegrable 0 T
  have hUV : IntervalIntegrable (fun t : ℝ => inPhaseWaveform T k t * quadratureWaveform T k t)
      MeasureTheory.volume 0 T :=
    (hU.mul hV).intervalIntegrable 0 T
  have hVU : IntervalIntegrable (fun t : ℝ => quadratureWaveform T k t * inPhaseWaveform T k t)
      MeasureTheory.volume 0 T :=
    (hV.mul hU).intervalIntegrable 0 T
  have h1 := hUU.const_mul (a * a)
  have h2 := hUV.const_mul (a * b)
  have h3 := hVU.const_mul (b * a)
  have h4 := hVV.const_mul (b * b)
  have h12 := h1.add h2
  have h123 := h12.add h3
  have h1234 := h123.add h4
  have hrewrite : (∫ t in (0 : ℝ)..T, iqWaveform a b T k t * iqWaveform a b T k t)
      = ∫ t in (0 : ℝ)..T, ((a * a) * (inPhaseWaveform T k t * inPhaseWaveform T k t)
          + (a * b) * (inPhaseWaveform T k t * quadratureWaveform T k t)
          + (b * a) * (quadratureWaveform T k t * inPhaseWaveform T k t)
          + (b * b) * (quadratureWaveform T k t * quadratureWaveform T k t)) := by
    apply intervalIntegral.integral_congr
    intro x _
    change iqWaveform a b T k x * iqWaveform a b T k x = _
    unfold iqWaveform
    ring
  rw [hrewrite]
  have hsplit1 := intervalIntegral.integral_add h123 h4
  have hsplit2 := intervalIntegral.integral_add h12 h3
  have hsplit3 := intervalIntegral.integral_add h1 h2
  simp only [intervalIntegral.integral_const_mul] at hsplit1 hsplit2 hsplit3 ⊢
  rw [hsplit1, hsplit2, hsplit3]
  have hNormU := inPhaseWaveform_norm T k hT hk
  have hNormV := quadratureWaveform_norm T k hT hk
  have hOrth := inPhaseWaveform_quadratureWaveform_orthogonal T k hT hk
  have hVU0 : (∫ t in (0 : ℝ)..T, quadratureWaveform T k t * inPhaseWaveform T k t) = 0 := by
    have hcongr : (∫ t in (0 : ℝ)..T, quadratureWaveform T k t * inPhaseWaveform T k t)
        = (∫ t in (0 : ℝ)..T, inPhaseWaveform T k t * quadratureWaveform T k t) := by
      apply intervalIntegral.integral_congr
      intro x _
      change quadratureWaveform T k x * inPhaseWaveform T k x
        = inPhaseWaveform T k x * quadratureWaveform T k x
      exact mul_comm _ _
    rw [hcongr, hOrth]
  rw [hNormU, hNormV, hOrth, hVU0]
  ring

/-- Projecting `a * u + b * v` against the in-phase waveform recovers
`a`. -/
theorem iqWaveform_projection_inPhase (a b T : ℝ) (k : ℕ) (hT : 0 < T)
    (hk : 1 ≤ k) :
    (∫ t in (0 : ℝ)..T, iqWaveform a b T k t * inPhaseWaveform T k t) = a := by
  have hU : Continuous (fun t : ℝ => inPhaseWaveform T k t) := by
    unfold inPhaseWaveform
    fun_prop
  have hV : Continuous (fun t : ℝ => quadratureWaveform T k t) := by
    unfold quadratureWaveform
    fun_prop
  have hUU : IntervalIntegrable (fun t : ℝ => inPhaseWaveform T k t * inPhaseWaveform T k t)
      MeasureTheory.volume 0 T :=
    (hU.mul hU).intervalIntegrable 0 T
  have hVU : IntervalIntegrable (fun t : ℝ => quadratureWaveform T k t * inPhaseWaveform T k t)
      MeasureTheory.volume 0 T :=
    (hV.mul hU).intervalIntegrable 0 T
  have h1 := hUU.const_mul a
  have h2 := hVU.const_mul b
  have hrewrite : (∫ t in (0 : ℝ)..T, iqWaveform a b T k t * inPhaseWaveform T k t)
      = ∫ t in (0 : ℝ)..T, (a * (inPhaseWaveform T k t * inPhaseWaveform T k t)
          + b * (quadratureWaveform T k t * inPhaseWaveform T k t)) := by
    apply intervalIntegral.integral_congr
    intro x _
    change iqWaveform a b T k x * inPhaseWaveform T k x = _
    unfold iqWaveform
    ring
  rw [hrewrite]
  have hsplit := intervalIntegral.integral_add h1 h2
  simp only [intervalIntegral.integral_const_mul] at hsplit ⊢
  rw [hsplit]
  have hNormU := inPhaseWaveform_norm T k hT hk
  have hOrth := inPhaseWaveform_quadratureWaveform_orthogonal T k hT hk
  have hVU0 : (∫ t in (0 : ℝ)..T, quadratureWaveform T k t * inPhaseWaveform T k t) = 0 := by
    have hcongr : (∫ t in (0 : ℝ)..T, quadratureWaveform T k t * inPhaseWaveform T k t)
        = (∫ t in (0 : ℝ)..T, inPhaseWaveform T k t * quadratureWaveform T k t) := by
      apply intervalIntegral.integral_congr
      intro x _
      change quadratureWaveform T k x * inPhaseWaveform T k x
        = inPhaseWaveform T k x * quadratureWaveform T k x
      exact mul_comm _ _
    rw [hcongr, hOrth]
  rw [hNormU, hVU0]
  ring

/-- Projecting `a * u + b * v` against the quadrature waveform
recovers `b`. -/
theorem iqWaveform_projection_quadrature (a b T : ℝ) (k : ℕ) (hT : 0 < T)
    (hk : 1 ≤ k) :
    (∫ t in (0 : ℝ)..T, iqWaveform a b T k t * quadratureWaveform T k t) = b := by
  have hU : Continuous (fun t : ℝ => inPhaseWaveform T k t) := by
    unfold inPhaseWaveform
    fun_prop
  have hV : Continuous (fun t : ℝ => quadratureWaveform T k t) := by
    unfold quadratureWaveform
    fun_prop
  have hUV : IntervalIntegrable (fun t : ℝ => inPhaseWaveform T k t * quadratureWaveform T k t)
      MeasureTheory.volume 0 T :=
    (hU.mul hV).intervalIntegrable 0 T
  have hVV : IntervalIntegrable (fun t : ℝ => quadratureWaveform T k t * quadratureWaveform T k t)
      MeasureTheory.volume 0 T :=
    (hV.mul hV).intervalIntegrable 0 T
  have h1 := hUV.const_mul a
  have h2 := hVV.const_mul b
  have hrewrite : (∫ t in (0 : ℝ)..T, iqWaveform a b T k t * quadratureWaveform T k t)
      = ∫ t in (0 : ℝ)..T, (a * (inPhaseWaveform T k t * quadratureWaveform T k t)
          + b * (quadratureWaveform T k t * quadratureWaveform T k t)) := by
    apply intervalIntegral.integral_congr
    intro x _
    change iqWaveform a b T k x * quadratureWaveform T k x = _
    unfold iqWaveform
    ring
  rw [hrewrite]
  have hsplit := intervalIntegral.integral_add h1 h2
  simp only [intervalIntegral.integral_const_mul] at hsplit ⊢
  rw [hsplit]
  have hNormV := quadratureWaveform_norm T k hT hk
  have hOrth := inPhaseWaveform_quadratureWaveform_orthogonal T k hT hk
  rw [hOrth, hNormV]
  ring

/-- Headline correctness: the two waveforms are orthonormal on
`[0, T]`, the energy of a constant-coefficient combination is the sum
of the squared coefficients, and both projections recover the
coefficients. -/
theorem iqBasis_orthonormal_energy_and_projection (a b T : ℝ) (k : ℕ)
    (hT : 0 < T) (hk : 1 ≤ k) :
    (∫ t in (0 : ℝ)..T, inPhaseWaveform T k t * inPhaseWaveform T k t) = 1 ∧
      (∫ t in (0 : ℝ)..T, quadratureWaveform T k t * quadratureWaveform T k t) = 1 ∧
      (∫ t in (0 : ℝ)..T, inPhaseWaveform T k t * quadratureWaveform T k t) = 0 ∧
      (∫ t in (0 : ℝ)..T, iqWaveform a b T k t * iqWaveform a b T k t)
        = a ^ 2 + b ^ 2 ∧
      (∫ t in (0 : ℝ)..T, iqWaveform a b T k t * inPhaseWaveform T k t) = a ∧
      (∫ t in (0 : ℝ)..T, iqWaveform a b T k t * quadratureWaveform T k t) = b := by
  exact ⟨inPhaseWaveform_norm T k hT hk, quadratureWaveform_norm T k hT hk,
    inPhaseWaveform_quadratureWaveform_orthogonal T k hT hk,
    iqWaveform_energy a b T k hT hk,
    iqWaveform_projection_inPhase a b T k hT hk,
    iqWaveform_projection_quadrature a b T k hT hk⟩

/-! ## D. Concrete validations and carrier mismatch -/

/-- First-carrier validation: coefficients `3` and `4` at `k = 1` give
energy `25`. -/
lemma iqWaveform_energy_firstCarrier_example (T : ℝ) (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, iqWaveform 3 4 T 1 t * iqWaveform 3 4 T 1 t) = 25 := by
  exact (iqWaveform_energy 3 4 T 1 hT le_rfl).trans (by norm_num)

/-- Second-carrier validation: coefficients `3` and `4` at `k = 2`
project to `3` on the in-phase waveform and to `4` on the quadrature
waveform. -/
lemma iqWaveform_projection_secondCarrier_example (T : ℝ) (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, iqWaveform 3 4 T 2 t * inPhaseWaveform T 2 t) = 3 ∧
      (∫ t in (0 : ℝ)..T, iqWaveform 3 4 T 2 t * quadratureWaveform T 2 t) = 4 := by
  exact ⟨iqWaveform_projection_inPhase 3 4 T 2 hT (by decide),
    iqWaveform_projection_quadrature 3 4 T 2 hT (by decide)⟩

/-- Carrier mismatch need not be orthogonal: a quarter-cycle carrier
on the unit window has a nonzero mixed sine-cosine integral, so the
integer-carrier hypothesis cannot be dropped. -/
lemma quarterCycleCarrier_crossIntegral_ne_zero :
    (∫ t in (0 : ℝ)..1, Real.cos (Real.pi * t / 2) * Real.sin (Real.pi * t / 2))
      ≠ 0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcpos : 0 < Real.pi / 2 := by positivity
  have hcne : (Real.pi / 2 : ℝ) ≠ 0 := ne_of_gt hcpos
  have hrewrite1 : (∫ t in (0 : ℝ)..1, Real.cos (Real.pi * t / 2) * Real.sin (Real.pi * t / 2))
      = (∫ t in (0 : ℝ)..1, Real.sin (Real.pi * t / 2) * Real.cos (Real.pi * t / 2)) := by
    apply intervalIntegral.integral_congr
    intro x _
    change Real.cos (Real.pi * x / 2) * Real.sin (Real.pi * x / 2)
      = Real.sin (Real.pi * x / 2) * Real.cos (Real.pi * x / 2)
    exact mul_comm _ _
  have hrewrite2 : (∫ t in (0 : ℝ)..1, Real.sin (Real.pi * t / 2) * Real.cos (Real.pi * t / 2))
      = ∫ t in (0 : ℝ)..1, (fun u : ℝ => Real.sin u * Real.cos u) ((Real.pi / 2) * t) := by
    apply intervalIntegral.integral_congr
    intro x _
    have harg : Real.pi * x / 2 = (Real.pi / 2) * x := by ring
    change Real.sin (Real.pi * x / 2) * Real.cos (Real.pi * x / 2)
      = (fun u : ℝ => Real.sin u * Real.cos u) ((Real.pi / 2) * x)
    rw [harg]
  rw [hrewrite1, hrewrite2]
  have hcomp := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun u : ℝ => Real.sin u * Real.cos u) hcne
  rw [hcomp]
  simp only [smul_eq_mul]
  have hc0 : (Real.pi / 2 : ℝ) * 0 = 0 := by ring
  have hc1 : (Real.pi / 2 : ℝ) * 1 = Real.pi / 2 := by ring
  rw [hc0, hc1]
  rw [integral_sin_mul_cos₁]
  have hsin2 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  simp [hsin2, hpi]

end PhyslibExt.Communications.FiniteIQSignalSpace
