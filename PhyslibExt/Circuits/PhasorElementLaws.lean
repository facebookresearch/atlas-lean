/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.RMSAveragePower
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Phasor element laws

## i. Overview

For RMS phasors at positive angular frequency, the resistor,
inductor and capacitor laws are exactly the time-domain laws
`v = R i`, `v = L di/dt`, `i = C dv/dt` under the canonical RMS
waveform from `PhyslibExt.Circuits.RMSAveragePower` (imported,
not copied): an inductor contributes `i omega L`, a capacitor
`1 / (i omega C)`, quadrature is a quarter-period lead, and the
inverse forms need positive resistance.

## ii. Key results

- `phasor_element_laws`: the resistor, inductor and capacitor
  laws, each equivalent in time-domain and phasor form.
- `inductor_voltage_leads_current`: quadrature as a
  quarter-period lead.

## iii. Table of contents

- A. Phasor element laws

## iv. References

- C. K. Alexander and M. N. O. Sadiku, *Fundamentals of
  Electric Circuits*, seventh edition, McGraw-Hill, 2021:
  phasor relationships for R, L, and C.

## A. Phasor element laws
-/

@[expose] public section

namespace PhyslibExt.Circuits.PhasorElementLaws

open PhyslibExt.Circuits.RMSAveragePower

/-! ### Private helpers -/

/-- Real scalars factor out of the phasor waveform. -/
private theorem rmsWaveform_real_scale (R : ℝ) (W : ℂ) (ω t : ℝ) :
    rmsWaveform ((R : ℂ) * W) ω t = R * rmsWaveform W ω t := by
  unfold rmsWaveform
  rw [mul_assoc, Complex.re_ofReal_mul]
  ring

/-- Quarter-period time algebra. -/
private theorem mul_quarter_period {ω : ℝ} (hω : ω ≠ 0) :
    ω * (Real.pi / (2 * ω)) = Real.pi / 2 := by
  have h2ω : (2 : ℝ) * ω ≠ 0 := mul_ne_zero (by norm_num) hω
  field_simp

/-- Shifted-time algebra. -/
private theorem mul_add_quarter_period {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    ω * (t + Real.pi / (2 * ω)) = ω * t + Real.pi / 2 := by
  have h := mul_quarter_period hω
  rw [mul_add, h]

/-- The complex exponential at a quarter turn is `i`. -/
private theorem exp_pi_div_two :
    Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  have hcast : ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 := by norm_cast
  rw [hcast]
  exact Complex.exp_pi_div_two_mul_I

/-- The waveform at a quarter period sees the imaginary part of the phasor. -/
private theorem rmsWaveform_at_quarter (V : ℂ) {ω : ℝ} (hω : ω ≠ 0) :
    rmsWaveform V ω (Real.pi / (2 * ω)) = Real.sqrt 2 * (-V.im) := by
  have hmul := mul_quarter_period hω
  unfold rmsWaveform
  rw [hmul, exp_pi_div_two, Complex.mul_I_re]

/-- Multiplying a phasor by `i` shifts its waveform by a quarter period. -/
private theorem rmsWaveform_mul_I_shift (W : ℂ) {ω : ℝ} (hω : 0 < ω) (t : ℝ) :
    rmsWaveform (Complex.I * W) ω t = rmsWaveform W ω (t + Real.pi / (2 * ω)) := by
  have hω' : ω ≠ 0 := ne_of_gt hω
  have htime := mul_add_quarter_period hω' t
  have hexp : Complex.exp (((ω * (t + Real.pi / (2 * ω)) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) * Complex.I := by
    rw [htime]
    have hsplit : (((ω * t + Real.pi / 2 : ℝ) : ℂ)) * Complex.I
        = ((ω * t : ℝ) : ℂ) * Complex.I + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hsplit, Complex.exp_add, exp_pi_div_two]
  unfold rmsWaveform
  rw [hexp]
  have hring : (Complex.I * W) * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)
      = W * (Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) * Complex.I) := by ring
  rw [hring]

/-! ### Representation lemmas -/

/-- Differentiating the declared sinusoid multiplies its phasor by `i ω` (the
`exp (+i ω t)` convention). -/
lemma hasDerivAt_rmsWaveform (V : ℂ) (ω t : ℝ) :
    HasDerivAt (rmsWaveform V ω) (rmsWaveform (Complex.I * (ω : ℂ) * V) ω t) t := by
  have h1 : HasDerivAt (fun t : ℝ => ω * t) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have h2 : HasDerivAt (fun t : ℝ => ((ω * t : ℝ) : ℂ)) ((ω : ℝ) : ℂ) t :=
    h1.ofReal_comp
  have h3 : HasDerivAt (fun t : ℝ => ((ω * t : ℝ) : ℂ) * Complex.I)
      (((ω : ℝ) : ℂ) * Complex.I) t :=
    h2.mul_const Complex.I
  have h4 : HasDerivAt (fun t : ℝ => Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) * (((ω : ℝ) : ℂ) * Complex.I)) t :=
    h3.cexp
  have h5 : HasDerivAt (fun t : ℝ => V * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I))
      (V * (Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) * (((ω : ℝ) : ℂ) * Complex.I))) t :=
    h4.const_mul V
  have h6 : HasDerivAt (fun t : ℝ => (V * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)).re)
      ((V * (Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) * (((ω : ℝ) : ℂ) * Complex.I))).re) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h5
  have h7 : HasDerivAt
      (fun t : ℝ => Real.sqrt 2 * (V * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)).re)
      (Real.sqrt 2 * ((V * (Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) *
        (((ω : ℝ) : ℂ) * Complex.I))).re)) t :=
    h6.const_mul (Real.sqrt 2)
  have hring : V * (Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) * (((ω : ℝ) : ℂ) * Complex.I))
      = (Complex.I * (ω : ℂ) * V) * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) := by
    ring
  unfold rmsWaveform
  rw [← hring]
  exact h7

/-- At a nonzero frequency the RMS waveform determines its phasor. -/
lemma rmsWaveform_eq_iff {ω : ℝ} (hω : ω ≠ 0) (V W : ℂ) :
    rmsWaveform V ω = rmsWaveform W ω ↔ V = W := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h (Real.pi / (2 * ω))
    rw [rmsWaveform_at_zero, rmsWaveform_at_zero] at h0
    rw [rmsWaveform_at_quarter _ hω, rmsWaveform_at_quarter _ hω] at h1
    have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_ne_zero').mpr (by norm_num)
    have hre : V.re = W.re := mul_left_cancel₀ hsqrt h0
    have him : V.im = W.im := neg_inj.mp (mul_left_cancel₀ hsqrt h1)
    exact Complex.ext hre him
  · intro h
    rw [h]

/-! ### Element laws as phasor equations -/

/-- **Resistor.** For sinusoidal `v`, `i` with RMS phasors `V`, `I` at `ω > 0`, Ohm's law
`v = R i` at every time is equivalent to the phasor equation `V = R I`. -/
lemma resistor_law_iff_phasor (R : ℝ) (hR : 0 ≤ R) {ω : ℝ} (hω : 0 < ω) (V I : ℂ)
    (v i : ℝ → ℝ) (hv : ∀ t, v t = rmsWaveform V ω t) (hi : ∀ t, i t = rmsWaveform I ω t) :
    (∀ t, v t = R * i t) ↔ V = (R : ℂ) * I := by
  constructor
  · intro h
    have hfun : rmsWaveform V ω = rmsWaveform ((R : ℂ) * I) ω := by
      funext t
      have ht := h t
      rw [hv t, hi t] at ht
      have hs := rmsWaveform_real_scale R I ω t
      rw [← hs] at ht
      exact ht
    exact (rmsWaveform_eq_iff (ne_of_gt hω) V _).mp hfun
  · intro h t
    rw [hv t, hi t, h]
    exact rmsWaveform_real_scale R I ω t

/-- **Inductor.** For sinusoidal `v`, `i` with RMS phasors `V`, `I` at `ω > 0`, the law
`v = L di/dt` at every time is equivalent to the phasor equation `V = i ω L I`. -/
lemma inductor_law_iff_phasor (L : ℝ) (hL : 0 < L) {ω : ℝ} (hω : 0 < ω) (V I : ℂ)
    (v i : ℝ → ℝ) (hv : ∀ t, v t = rmsWaveform V ω t) (hi : ∀ t, i t = rmsWaveform I ω t) :
    (∀ t, v t = L * deriv i t) ↔ V = Complex.I * (ω : ℂ) * (L : ℂ) * I := by
  have hfun : i = rmsWaveform I ω := funext hi
  have hder : ∀ t, deriv i t = rmsWaveform (Complex.I * (ω : ℂ) * I) ω t := by
    intro t
    rw [hfun]
    exact (hasDerivAt_rmsWaveform I ω t).deriv
  have hscale : ∀ t, L * rmsWaveform (Complex.I * (ω : ℂ) * I) ω t
      = rmsWaveform (Complex.I * (ω : ℂ) * (L : ℂ) * I) ω t := by
    intro t
    have h := rmsWaveform_real_scale L (Complex.I * (ω : ℂ) * I) ω t
    have hring : (L : ℂ) * (Complex.I * (ω : ℂ) * I)
        = Complex.I * (ω : ℂ) * (L : ℂ) * I := by ring
    rw [hring] at h
    exact h.symm
  constructor
  · intro h
    have hfun' : rmsWaveform V ω
        = rmsWaveform (Complex.I * (ω : ℂ) * (L : ℂ) * I) ω := by
      funext t
      have ht := h t
      rw [hv t, hder t, hscale t] at ht
      exact ht
    exact (rmsWaveform_eq_iff (ne_of_gt hω) _ _).mp hfun'
  · intro h t
    rw [hv t, hder t, hscale t, h]

/-- **Capacitor.** For sinusoidal `v`, `i` with RMS phasors `V`, `I` at `ω > 0`, the law
`i = C dv/dt` at every time is equivalent to the phasor equation `I = i ω C V`. -/
lemma capacitor_law_iff_phasor (C : ℝ) (hC : 0 < C) {ω : ℝ} (hω : 0 < ω) (V I : ℂ)
    (v i : ℝ → ℝ) (hv : ∀ t, v t = rmsWaveform V ω t) (hi : ∀ t, i t = rmsWaveform I ω t) :
    (∀ t, i t = C * deriv v t) ↔ I = Complex.I * (ω : ℂ) * (C : ℂ) * V := by
  have hfun : v = rmsWaveform V ω := funext hv
  have hder : ∀ t, deriv v t = rmsWaveform (Complex.I * (ω : ℂ) * V) ω t := by
    intro t
    rw [hfun]
    exact (hasDerivAt_rmsWaveform V ω t).deriv
  have hscale : ∀ t, C * rmsWaveform (Complex.I * (ω : ℂ) * V) ω t
      = rmsWaveform (Complex.I * (ω : ℂ) * (C : ℂ) * V) ω t := by
    intro t
    have h := rmsWaveform_real_scale C (Complex.I * (ω : ℂ) * V) ω t
    have hring : (C : ℂ) * (Complex.I * (ω : ℂ) * V)
        = Complex.I * (ω : ℂ) * (C : ℂ) * V := by ring
    rw [hring] at h
    exact h.symm
  constructor
  · intro h
    have hfun' : rmsWaveform I ω
        = rmsWaveform (Complex.I * (ω : ℂ) * (C : ℂ) * V) ω := by
      funext t
      have ht := h t
      rw [hi t, hder t, hscale t] at ht
      exact ht
    exact (rmsWaveform_eq_iff (ne_of_gt hω) _ _).mp hfun'
  · intro h t
    rw [hi t, hder t, hscale t, h]

/-- **Phasor element laws.** Under `R ≥ 0`, `L, C > 0`, `ω > 0` and the RMS
`exp (+i ω t)` representation of `v` and `i`, the real resistor, inductor and capacitor laws
are equivalent to `V = R I`, `V = i ω L I` and `I = i ω C V`. -/
lemma phasor_element_laws (R L C : ℝ) (hR : 0 ≤ R) (hL : 0 < L) (hC : 0 < C) {ω : ℝ}
    (hω : 0 < ω) (V I : ℂ) (v i : ℝ → ℝ) (hv : ∀ t, v t = rmsWaveform V ω t)
    (hi : ∀ t, i t = rmsWaveform I ω t) :
    ((∀ t, v t = R * i t) ↔ V = (R : ℂ) * I) ∧
      ((∀ t, v t = L * deriv i t) ↔ V = Complex.I * (ω : ℂ) * (L : ℂ) * I) ∧
      ((∀ t, i t = C * deriv v t) ↔ I = Complex.I * (ω : ℂ) * (C : ℂ) * V) := by
  exact ⟨resistor_law_iff_phasor R hR hω V I v i hv hi,
    inductor_law_iff_phasor L hL hω V I v i hv hi,
    capacitor_law_iff_phasor C hC hω V I v i hv hi⟩

/-! ### Impedance and admittance forms (nonzero denominators only) -/

/-- Resistor admittance form `I = V / R`, valid for `R > 0`. -/
lemma resistor_phasor_iff_admittance (R : ℝ) (hR : 0 < R) (V I : ℂ) :
    V = (R : ℂ) * I ↔ I = V / (R : ℂ) := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  rw [eq_div_iff_mul_eq hR']
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    rw [← h]
    ring

/-- Inductor admittance form `I = V / (i ω L)`, valid for `ω > 0` and `L > 0`. -/
lemma inductor_phasor_iff_admittance (L : ℝ) (hL : 0 < L) {ω : ℝ} (hω : 0 < ω) (V I : ℂ) :
    V = Complex.I * (ω : ℂ) * (L : ℂ) * I ↔ I = V / (Complex.I * (ω : ℂ) * (L : ℂ)) := by
  have hc : Complex.I * (ω : ℂ) * (L : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ne_of_gt hω))
      (by exact_mod_cast ne_of_gt hL)
  rw [eq_div_iff_mul_eq hc]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    rw [← h]
    ring

/-- Capacitor impedance form `V = I / (i ω C)`, valid for `ω > 0` and `C > 0`. -/
lemma capacitor_phasor_iff_impedance (C : ℝ) (hC : 0 < C) {ω : ℝ} (hω : 0 < ω) (V I : ℂ) :
    I = Complex.I * (ω : ℂ) * (C : ℂ) * V ↔ V = I / (Complex.I * (ω : ℂ) * (C : ℂ)) := by
  have hc : Complex.I * (ω : ℂ) * (C : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ne_of_gt hω))
      (by exact_mod_cast ne_of_gt hC)
  rw [eq_div_iff_mul_eq hc]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    rw [← h]
    ring

/-! ### Validation: quadrature, `R = 0`, and DC -/

/-- Inductor quadrature: under `V = i ω L I` the voltage waveform is `ω L` times the current
waveform advanced by a quarter period `π / (2 ω)`. -/
lemma inductor_voltage_leads_current (L : ℝ) (hL : 0 < L) {ω : ℝ} (hω : 0 < ω) (V I : ℂ)
    (h : V = Complex.I * (ω : ℂ) * (L : ℂ) * I) (t : ℝ) :
    rmsWaveform V ω t = ω * L * rmsWaveform I ω (t + Real.pi / (2 * ω)) := by
  have hV : V = Complex.I * ((((ω * L : ℝ)) : ℂ) * I) := by
    rw [h]
    push_cast
    ring
  rw [hV, rmsWaveform_mul_I_shift _ hω _, rmsWaveform_real_scale]

/-- Capacitor quadrature: under `I = i ω C V` the current waveform is `ω C` times the voltage
waveform advanced by a quarter period `π / (2 ω)`. -/
lemma capacitor_current_leads_voltage (C : ℝ) (hC : 0 < C) {ω : ℝ} (hω : 0 < ω) (V I : ℂ)
    (h : I = Complex.I * (ω : ℂ) * (C : ℂ) * V) (t : ℝ) :
    rmsWaveform I ω t = ω * C * rmsWaveform V ω (t + Real.pi / (2 * ω)) := by
  have hI : I = Complex.I * ((((ω * C : ℝ)) : ℂ) * V) := by
    rw [h]
    push_cast
    ring
  rw [hI, rmsWaveform_mul_I_shift _ hω _, rmsWaveform_real_scale]

/-- `R = 0` in the multiplicative equation: a short circuit `v = 0 * i` is equivalent to the
zero voltage phasor. -/
lemma short_circuit_law_iff_phasor {ω : ℝ} (hω : 0 < ω) (V I : ℂ) (v i : ℝ → ℝ)
    (hv : ∀ t, v t = rmsWaveform V ω t) (hi : ∀ t, i t = rmsWaveform I ω t) :
    (∀ t, v t = 0 * i t) ↔ V = 0 := by
  have h := resistor_law_iff_phasor 0 (le_refl 0) hω V I v i hv hi
  simpa using h

/-- At `R = 0` the admittance form is not equivalent to the multiplicative equation
(`V / 0 = 0` in Lean), so the nonzero-denominator guard is necessary. -/
lemma resistor_admittance_form_fails_at_zero :
    ¬ ∀ V I : ℂ, (V = ((0 : ℝ) : ℂ) * I ↔ I = V / ((0 : ℝ) : ℂ)) := by
  intro h
  have h01 := h 0 1
  simp at h01

/-- At DC (`ω = 0`) the RMS waveform is the constant `sqrt 2 * Re V`: the imaginary part of the
phasor is invisible. -/
lemma rmsWaveform_zero_frequency (V : ℂ) (t : ℝ) :
    rmsWaveform V 0 t = Real.sqrt 2 * V.re := by
  simp [rmsWaveform]

/-- At DC the real element laws do not determine the phasor equations: with `V = i`, `I = 0`
and unit `R`, `L`, both the resistor and the inductor law hold at every time, yet neither
`V = R I` nor `V = i ω L I` holds. -/
lemma dc_element_laws_do_not_determine_phasor :
    ((∀ t, rmsWaveform Complex.I 0 t = 1 * rmsWaveform 0 0 t) ∧
        Complex.I ≠ ((1 : ℝ) : ℂ) * 0) ∧
      ((∀ t, rmsWaveform Complex.I 0 t = 1 * deriv (rmsWaveform 0 0) t) ∧
        Complex.I ≠ Complex.I * ((0 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) * 0) := by
  have h0 : rmsWaveform (0 : ℂ) 0 = fun _ => 0 := by
    funext t
    simp [rmsWaveform_zero_frequency]
  have hderiv : ∀ t, deriv (rmsWaveform 0 0) t = 0 := by
    intro t
    rw [h0]
    exact deriv_const t 0
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro t
    simp [rmsWaveform_zero_frequency]
  · simp
  · intro t
    rw [rmsWaveform_zero_frequency, hderiv t]
    simp
  · simp

/-- At DC the inductor admittance form is not equivalent to the phasor equation: the
denominator `i ω L` vanishes. -/
lemma inductor_admittance_form_fails_at_dc (L : ℝ) :
    ¬ ∀ V I : ℂ, (V = Complex.I * ((0 : ℝ) : ℂ) * (L : ℂ) * I ↔
      I = V / (Complex.I * ((0 : ℝ) : ℂ) * (L : ℂ))) := by
  intro h
  have h01 := h 0 1
  simp at h01

end PhyslibExt.Circuits.PhasorElementLaws
