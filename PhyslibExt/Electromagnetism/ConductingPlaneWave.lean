/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves

/-!
# Conducting plane waves and skin depth

Propagation of a monochromatic plane wave in a homogeneous isotropic
conducting medium, at the level of the squared propagation equation
and its explicit forward root.

## i. Overview

The medium is described by explicit real parameters: the absolute
permittivity `epsilon > 0`, the absolute permeability `mu > 0`, the
angular frequency `omega > 0`, and the conductivity `sigma ≥ 0`; no
relative-permittivity or vacuum-constant substitution is made. With
the phasor time convention `exp (+i * omega * t)` and a wave
travelling in the positive `z` direction as `exp (-gamma * z)`, the
propagation constant is required to satisfy the squared equation
`gamma ^ 2 = -omega ^ 2 * mu * epsilon + i * omega * mu * sigma`,
stated as `satisfiesDispersionEquation`. The forward root
`gamma = alpha + i * beta` is defined by explicit square-root
formulas for the attenuation constant `alpha` and the phase constant
`beta`; the squared equation alone does not select this root, since
the opposite root has the same square, so the sign conditions
`alpha ≥ 0` and `beta > 0` are part of the verification. At zero
conductivity the root reduces to the lossless wavenumber
`beta = omega * sqrt (mu * epsilon)` with no attenuation; for
`sigma > 0` the attenuation is strictly positive and the skin depth
`1 / alpha` is finite. Reversing the time convention without changing
signs negates the conductive term and gives a different equation
when `sigma > 0`.

Every result here is algebra about these explicit parameters and the
chosen root. The derivation of the squared propagation equation from
a region and material Maxwell provider for homogeneous permittivity,
permeability, and conductivity is an interface boundary that this
module does not discharge: `satisfiesDispersionEquation` is the exact
equation such a provider-side derivation must deliver, and no
provider is assumed or constructed here. The conductivity parameter
is the scalar in that equation; the dilute-carrier conductivity of
`PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves.conductivity`
is the constitutive notion behind it, and no theorem about that
notion is consumed here. Proofs proceed by unfolding the definitions
and applying positivity and the real square-root identities
`Real.sq_sqrt`; no regularity hypotheses beyond the displayed
positivity assumptions are needed.

## ii. Key results

- `propagationConstant_sq`, `propagationConstant_sq_eq`: the forward
  root satisfies the squared propagation equation.
- `dispersion_verification`: the bundled verification, combining the
  squared equation with the forward-root sign conditions.
- `attenuationConstant_zero_sigma`, `phaseConstant_zero_sigma`,
  `propagationConstant_zero_sigma`: at zero conductivity there is no
  attenuation and the phase constant is the lossless wavenumber.
- `skinDepth_pos_and_mul_eq_one`: with positive conductivity the skin
  depth is positive and reciprocal to the attenuation.
- `neg_propagationConstant_not_forward`: the opposite root has
  nonpositive real part and negative imaginary part, so it is not the
  forward attenuating root.
- `abs_exp_neg_propagationConstant_mul`: the modulus of
  `exp (-gamma * z)` at real depth `z` is the real decay
  `exp (-alpha * z)`.
- `planeWave_eq_re_forward_phasor_at_zero_sigma`: at zero
  conductivity the real cosine plane wave is the real part of the
  forward phasor `exp (+i * omega * t) * exp (-gamma * x)` of the
  declared convention.

## iii. Table of contents

- A. Declared propagation model
- B. Root choice and dispersion verification
- C. Lossless and skin-depth reductions
- D. Root exclusion and sign convention
- E. Travelling-wave and real-field consequences

## iv. References

- J. D. Jackson, *Classical Electrodynamics*, 3rd ed., Wiley, 1999,
  §7.5: propagation of electromagnetic waves in a conducting medium,
  the complex propagation constant, its attenuation and phase parts,
  and the skin depth.
- `PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves`, for the
  real cosine plane wave `planeWave` and the dilute-carrier
  conductivity `conductivity` referenced in Section E and above.
-/

@[expose] public section

noncomputable section

namespace PhyslibExt.Electromagnetism.ConductingPlaneWave

/-! ## A. Declared propagation model -/

/-- Attenuation constant `alpha` for positive medium parameters. -/
noncomputable def attenuationConstant (epsilon mu omega sigma : ℝ) : ℝ :=
  omega * Real.sqrt (mu * epsilon / 2) *
    Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1)

/-- Phase constant `beta` for positive medium parameters. -/
noncomputable def phaseConstant (epsilon mu omega sigma : ℝ) : ℝ :=
  omega * Real.sqrt (mu * epsilon / 2) *
    Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1)

/-- Forward propagation constant `gamma = alpha + i * beta`. -/
noncomputable def propagationConstant (epsilon mu omega sigma : ℝ) : ℂ :=
  (attenuationConstant epsilon mu omega sigma : ℂ) +
    Complex.I * (phaseConstant epsilon mu omega sigma : ℂ)

/-- Skin depth `1 / alpha`, meaningful when attenuation is positive. -/
noncomputable def skinDepth (epsilon mu omega sigma : ℝ) : ℝ :=
  1 / attenuationConstant epsilon mu omega sigma

/-- The squared propagation equation in complex form. -/
def satisfiesDispersionEquation (epsilon mu omega sigma : ℝ) (gamma : ℂ) : Prop :=
  gamma ^ 2 = (-(omega ^ 2 * mu * epsilon) : ℂ) +
    Complex.I * (omega * mu * sigma : ℂ)

/-! ## B. Root choice and dispersion verification -/

/-- Attenuation is nonnegative. -/
lemma attenuationConstant_nonneg (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 ≤ sigma) :
    0 ≤ attenuationConstant epsilon mu omega sigma := by
  unfold attenuationConstant
  apply mul_nonneg
  · apply le_of_lt
    positivity
  · exact Real.sqrt_nonneg _

/-- The phase constant is strictly positive. -/
lemma phaseConstant_pos (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 ≤ sigma) :
    0 < phaseConstant epsilon mu omega sigma := by
  unfold phaseConstant
  apply mul_pos
  · positivity
  · apply Real.sqrt_pos_of_pos
    have h := Real.sqrt_nonneg (1 + (sigma / (omega * epsilon)) ^ 2)
    linarith

/-- Positive conductivity gives strictly positive attenuation. -/
lemma attenuationConstant_pos_of_sigma_pos (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 < sigma) :
    0 < attenuationConstant epsilon mu omega sigma := by
  unfold attenuationConstant
  apply mul_pos
  · positivity
  · apply Real.sqrt_pos_of_pos
    have hs_sq_pos : 0 < (sigma / (omega * epsilon)) ^ 2 := by positivity
    have h1 : (1 : ℝ) < Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) := by
      rw [Real.lt_sqrt (by norm_num)]
      nlinarith [hs_sq_pos]
    linarith

/-- The propagation constant is its attenuation and phase parts. -/
lemma propagationConstant_eq (epsilon mu omega sigma : ℝ) :
    propagationConstant epsilon mu omega sigma =
      (attenuationConstant epsilon mu omega sigma : ℂ) +
        Complex.I * (phaseConstant epsilon mu omega sigma : ℂ) := by
  rfl

/-- Headline verification: the forward root satisfies the squared
propagation equation for the stated sign convention. -/
theorem propagationConstant_sq (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 ≤ sigma) :
    satisfiesDispersionEquation epsilon mu omega sigma
      (propagationConstant epsilon mu omega sigma) := by
  unfold satisfiesDispersionEquation
  have h_diff : (attenuationConstant epsilon mu omega sigma) ^ 2 -
      (phaseConstant epsilon mu omega sigma) ^ 2 =
      -(omega ^ 2 * mu * epsilon) := by
    unfold attenuationConstant phaseConstant
    have hm_nonneg : 0 ≤ mu * epsilon / 2 := by positivity
    have hr_ge_one : 1 ≤ Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) := by
      rw [Real.one_le_sqrt]
      have h := sq_nonneg (sigma / (omega * epsilon))
      linarith
    have hr_sub_nonneg : 0 ≤ Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1 := by
      linarith
    have hsq_m : (Real.sqrt (mu * epsilon / 2)) ^ 2 = mu * epsilon / 2 :=
      Real.sq_sqrt hm_nonneg
    have hsq_sub : (Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1)) ^ 2 =
        Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1 :=
      Real.sq_sqrt hr_sub_nonneg
    have hr_add_nonneg : 0 ≤ Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1 := by
      have h := Real.sqrt_nonneg (1 + (sigma / (omega * epsilon)) ^ 2)
      linarith
    have hsq_add : (Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1)) ^ 2 =
        Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1 :=
      Real.sq_sqrt hr_add_nonneg
    have hα : (omega * Real.sqrt (mu * epsilon / 2) *
        Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1)) ^ 2 =
        omega ^ 2 * (mu * epsilon / 2) *
          (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1) := by
      rw [mul_pow, mul_pow, hsq_m, hsq_sub]
    have hβ : (omega * Real.sqrt (mu * epsilon / 2) *
        Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1)) ^ 2 =
        omega ^ 2 * (mu * epsilon / 2) *
          (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1) := by
      rw [mul_pow, mul_pow, hsq_m, hsq_add]
    rw [hα, hβ]
    ring
  have h_prod : 2 * (attenuationConstant epsilon mu omega sigma) *
      (phaseConstant epsilon mu omega sigma) =
      omega * mu * sigma := by
    unfold attenuationConstant phaseConstant
    have hm_nonneg : 0 ≤ mu * epsilon / 2 := by positivity
    have h_inner_nonneg : 0 ≤ (1 : ℝ) + (sigma / (omega * epsilon)) ^ 2 := by
      have h := sq_nonneg (sigma / (omega * epsilon))
      linarith
    have hr_sq : (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2)) ^ 2 =
        1 + (sigma / (omega * epsilon)) ^ 2 :=
      Real.sq_sqrt h_inner_nonneg
    have hr_ge_one : 1 ≤ Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) := by
      rw [Real.one_le_sqrt]
      have h := sq_nonneg (sigma / (omega * epsilon))
      linarith
    have hr_sub_nonneg : 0 ≤ Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1 := by
      linarith
    have hs_nonneg : 0 ≤ sigma / (omega * epsilon) := by positivity
    have hsq_m : (Real.sqrt (mu * epsilon / 2)) ^ 2 = mu * epsilon / 2 :=
      Real.sq_sqrt hm_nonneg
    have h_sqrt_mul : Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1) *
        Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1) =
        Real.sqrt ((Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1) *
          (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1)) := by
      rw [Real.sqrt_mul hr_sub_nonneg]
    have h_mul_eq : (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1) *
        (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1) =
        (sigma / (omega * epsilon)) ^ 2 := by
      have h : (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1) *
          (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1) =
          (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2)) ^ 2 - 1 := by ring
      rw [h, hr_sq]
      ring
    have h_sqrt_eq : Real.sqrt ((Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1) *
        (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1)) =
        sigma / (omega * epsilon) := by
      rw [h_mul_eq, Real.sqrt_sq_eq_abs, abs_of_nonneg hs_nonneg]
    have hωε_ne : omega * epsilon ≠ 0 := ne_of_gt (mul_pos homega hepsilon)
    have hB : (omega * Real.sqrt (mu * epsilon / 2)) ^ 2 =
        omega ^ 2 * (mu * epsilon / 2) := by
      rw [mul_pow, hsq_m]
    have hprod : (omega * Real.sqrt (mu * epsilon / 2) *
        Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1)) *
        (omega * Real.sqrt (mu * epsilon / 2) *
        Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1)) =
        (omega ^ 2 * (mu * epsilon / 2)) * (sigma / (omega * epsilon)) := by
      calc (omega * Real.sqrt (mu * epsilon / 2) *
          Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1)) *
          (omega * Real.sqrt (mu * epsilon / 2) *
          Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1))
          = ((omega * Real.sqrt (mu * epsilon / 2)) *
            (omega * Real.sqrt (mu * epsilon / 2))) *
            (Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1) *
            Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1)) := by ring
        _ = ((omega * Real.sqrt (mu * epsilon / 2)) ^ 2) *
            (Real.sqrt ((Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1) *
            (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1))) := by
            rw [h_sqrt_mul]
            ring
        _ = (omega ^ 2 * (mu * epsilon / 2)) * (sigma / (omega * epsilon)) := by
            rw [hB, h_sqrt_eq]
    calc 2 * (omega * Real.sqrt (mu * epsilon / 2) *
        Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1)) *
        (omega * Real.sqrt (mu * epsilon / 2) *
        Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1))
        = 2 * (((omega * Real.sqrt (mu * epsilon / 2) *
          Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1)) *
          (omega * Real.sqrt (mu * epsilon / 2) *
          Real.sqrt (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) + 1)))) := by ring
      _ = 2 * ((omega ^ 2 * (mu * epsilon / 2)) * (sigma / (omega * epsilon))) := by
          rw [hprod]
      _ = omega * mu * sigma := by
          field_simp
  have hz_re : (propagationConstant epsilon mu omega sigma).re =
      attenuationConstant epsilon mu omega sigma := by
    unfold propagationConstant
    simp
  have hz_im : (propagationConstant epsilon mu omega sigma).im =
      phaseConstant epsilon mu omega sigma := by
    unfold propagationConstant
    simp
  apply Complex.ext
  · rw [pow_two, Complex.mul_re, hz_re, hz_im]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, ← Complex.ofReal_pow]
    simp
    linear_combination h_diff
  · rw [pow_two, Complex.mul_im, hz_re, hz_im]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_im, ← Complex.ofReal_pow]
    simp
    linear_combination h_prod

/-- The same verification, with the squared equation written out. -/
theorem propagationConstant_sq_eq (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 ≤ sigma) :
    (propagationConstant epsilon mu omega sigma) ^ 2 =
      (-(omega ^ 2 * mu * epsilon) : ℂ) +
        Complex.I * (omega * mu * sigma : ℂ) := by
  have h := propagationConstant_sq epsilon mu omega sigma hepsilon hmu homega hsigma
  unfold satisfiesDispersionEquation at h
  exact h

/-- Headline bundle: the squared equation holds and the chosen root
is the forward attenuating one. -/
theorem dispersion_verification (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 ≤ sigma) :
    satisfiesDispersionEquation epsilon mu omega sigma
        (propagationConstant epsilon mu omega sigma) ∧
      0 ≤ attenuationConstant epsilon mu omega sigma ∧
      0 < phaseConstant epsilon mu omega sigma := by
  exact ⟨propagationConstant_sq epsilon mu omega sigma hepsilon hmu homega hsigma,
    attenuationConstant_nonneg epsilon mu omega sigma hepsilon hmu homega hsigma,
    phaseConstant_pos epsilon mu omega sigma hepsilon hmu homega hsigma⟩

/-! ## C. Lossless and skin-depth reductions -/

/-- Lossless reduction: at zero conductivity there is no attenuation. -/
lemma attenuationConstant_zero_sigma (epsilon mu omega : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega) :
    attenuationConstant epsilon mu omega 0 = 0 := by
  unfold attenuationConstant
  simp

/-- Lossless reduction: at zero conductivity the phase constant is
the lossless wavenumber. -/
lemma phaseConstant_zero_sigma (epsilon mu omega : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega) :
    phaseConstant epsilon mu omega 0 = omega * Real.sqrt (mu * epsilon) := by
  unfold phaseConstant
  simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Real.sqrt_one]
  have h_nonneg : 0 ≤ mu * epsilon / 2 := by positivity
  have h_eq : Real.sqrt (mu * epsilon / 2) * Real.sqrt 2 = Real.sqrt (mu * epsilon) := by
    rw [← Real.sqrt_mul h_nonneg]
    congr 1
    ring
  have h2 : (1 : ℝ) + 1 = 2 := by norm_num
  rw [h2]
  calc omega * Real.sqrt (mu * epsilon / 2) * Real.sqrt 2
      = omega * (Real.sqrt (mu * epsilon / 2) * Real.sqrt 2) := by ring
    _ = omega * Real.sqrt (mu * epsilon) := by rw [h_eq]

/-- Lossless reduction: at zero conductivity the propagation constant
is purely imaginary with the lossless wavenumber. -/
lemma propagationConstant_zero_sigma (epsilon mu omega : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega) :
    propagationConstant epsilon mu omega 0 =
      Complex.I * (omega * Real.sqrt (mu * epsilon) : ℂ) := by
  unfold propagationConstant
  rw [attenuationConstant_zero_sigma epsilon mu omega hepsilon hmu homega,
    phaseConstant_zero_sigma epsilon mu omega hepsilon hmu homega]
  simp

/-- With positive conductivity the skin depth is positive and
reciprocal to the attenuation. -/
lemma skinDepth_pos_and_mul_eq_one (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 < sigma) :
    0 < skinDepth epsilon mu omega sigma ∧
      attenuationConstant epsilon mu omega sigma *
        skinDepth epsilon mu omega sigma = 1 := by
  have hα := attenuationConstant_pos_of_sigma_pos epsilon mu omega sigma hepsilon hmu
    homega hsigma
  unfold skinDepth
  constructor
  · exact (one_div_pos).mpr hα
  · exact mul_one_div_cancel (ne_of_gt hα)

/-! ## D. Root exclusion and sign convention -/

/-- The opposite root has the same square but is not the forward
attenuating root: its real part is nonpositive and its imaginary
part is negative under the headline hypotheses. -/
lemma neg_propagationConstant_not_forward (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 ≤ sigma) :
    (-propagationConstant epsilon mu omega sigma).re ≤ 0 ∧
      (-propagationConstant epsilon mu omega sigma).im < 0 := by
  have hα := attenuationConstant_nonneg epsilon mu omega sigma hepsilon hmu homega hsigma
  have hβ := phaseConstant_pos epsilon mu omega sigma hepsilon hmu homega hsigma
  unfold propagationConstant
  simp [Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  constructor <;> linarith

/-- Sign-convention check: the equation with the opposite sign of the
conductive term is different from the stated equation when the
conductive term is nonzero, so reversing the time convention without
changing signs does not satisfy the same squared equation. -/
lemma opposite_sign_equation_ne (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 < sigma) :
    (-(omega ^ 2 * mu * epsilon) : ℂ) - Complex.I * (omega * mu * sigma : ℂ) ≠
      (-(omega ^ 2 * mu * epsilon) : ℂ) + Complex.I * (omega * mu * sigma : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_im, ← Complex.ofReal_pow] at him
  have hx : 0 < omega * mu * sigma := by positivity
  linarith

/-! ## E. Travelling-wave and real-field consequences -/

/-- Attenuation of the travelling phasor: for real depth `z`, the
modulus of `exp (-gamma * z)` is the real exponential decay given by
the attenuation constant. -/
lemma abs_exp_neg_propagationConstant_mul (epsilon mu omega sigma : ℝ)
    (z : ℝ) :
    ‖Complex.exp
        (-propagationConstant epsilon mu omega sigma * (z : ℂ))‖ =
      Real.exp (-attenuationConstant epsilon mu omega sigma * z) := by
  rw [Complex.norm_exp]
  congr 1
  unfold propagationConstant
  simp [Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]

/-- At zero conductivity, the real cosine plane wave with wavenumber
the phase constant `beta` is the real part of
`exp (i * (beta * x - omega * t)) * E0`. This is the complex conjugate
of the forward phasor `exp (i * (omega * t - beta * x)) * E0` of the
declared convention, that is the phasor of the opposite time
convention; the two have the same real part because cosine is even,
so this identity does not check the sign convention. The phasor of
the declared convention is
`planeWave_eq_re_forward_phasor_at_zero_sigma`. -/
lemma planeWave_eq_re_phasor_at_zero_sigma (E0 epsilon mu omega : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega) (x t : ℝ) :
    PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves.planeWave
        E0 (phaseConstant epsilon mu omega 0) omega x t =
      (Complex.exp (Complex.I *
        ((phaseConstant epsilon mu omega 0 * x - omega * t : ℝ) : ℂ)) * (E0 : ℂ)).re := by
  unfold PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves.planeWave
  have harg : Complex.I * (((phaseConstant epsilon mu omega 0 * x - omega * t : ℝ)) : ℂ) =
      ((((phaseConstant epsilon mu omega 0 * x - omega * t : ℝ))) : ℂ) * Complex.I := by
    rw [mul_comm]
  rw [harg]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [Complex.exp_ofReal_mul_I_re]
  ring

/-- At zero conductivity, the real cosine plane wave with wavenumber
the phase constant is the real part of the forward phasor of the
declared convention, `exp (+i * omega * t) * exp (-gamma * x) * E0`
with `gamma` the propagation constant. -/
lemma planeWave_eq_re_forward_phasor_at_zero_sigma (E0 epsilon mu omega : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega) (x t : ℝ) :
    PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves.planeWave
        E0 (phaseConstant epsilon mu omega 0) omega x t =
      (Complex.exp (Complex.I * ((omega * t : ℝ) : ℂ)) *
        Complex.exp (-propagationConstant epsilon mu omega 0 * (x : ℂ)) *
          (E0 : ℂ)).re := by
  unfold PhyslibExt.Electromagnetism.ElectrostaticsAndLinearWaves.planeWave
  rw [← Complex.exp_add]
  have harg : Complex.I * ((omega * t : ℝ) : ℂ) +
      -propagationConstant epsilon mu omega 0 * (x : ℂ) =
      ((omega * t - phaseConstant epsilon mu omega 0 * x : ℝ) : ℂ) * Complex.I := by
    rw [propagationConstant_eq, attenuationConstant_zero_sigma epsilon mu omega hepsilon hmu
      homega]
    push_cast
    ring
  rw [harg]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [Complex.exp_ofReal_mul_I_re, ← Real.cos_neg, neg_sub]
  ring

end PhyslibExt.Electromagnetism.ConductingPlaneWave
