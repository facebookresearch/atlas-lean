/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Fourier normalization: hertz versus angular frequency

Two normalizations of the Fourier transform on `ℝ` are in common use, and
they differ by where the factor `2π` sits:

* hertz (cycles per unit time): `F f ξ = ∫ t, e^{-2πitξ} f t`, and
* angular frequency (radians per unit time): `F_ω f ω = ∫ t, e^{-iωt} f t`,

related by `ω = 2πξ`, i.e. `F_ω f ω = F f (ω / (2π))`. Neither convention
as used here carries a `1 / √(2π)` prefactor. Mathlib's `𝓕` is the hertz
form: on `ℝ`,
`𝓕 f w = ∫ v, Complex.exp (↑(-2 * π * v * w) * Complex.I) • f v`
(`Real.fourier_real_eq_integral_exp_smul` in
`Mathlib/Analysis/Fourier/FourierTransform.lean`).

This file defines the angular form `fourierAngular` and records, for
integrable `f : ℝ → ℂ`, the standard identities in both conventions:
`fourierAngular f ω = 𝓕 f (ω / (2π))`; conjugate symmetry
`𝓕 f (-ξ) = conj (𝓕 f ξ)` for real-valued `f`; the delay rules
`𝓕 (f (· - a)) ξ = e^{-2πiaξ} 𝓕 f ξ` and
`fourierAngular (f (· - a)) ω = e^{-iaω} fourierAngular f ω`; and the
modulation rule `𝓕 (e^{2πiat} f t) ξ = 𝓕 f (ξ - a)`. The `Integrable f`
hypotheses are kept on the statements (as in the classical `L¹` theory)
even where the integral identities also hold without them by the
junk-value convention for Bochner integrals. Transforms are taken of raw
functions into `ℂ` against Lebesgue measure on `ℝ`.

Provenance: these are the classical `L¹` Fourier identities, specialized
to Mathlib's hertz convention `𝓕` as displayed above; this file is the
control-theory roadmap's Fourier normalization sheet, leaf `SSC-U07.T01`
(clauses `SSC-F02.c02.b`, `SSC-U07.c01`). The normalizations, signs, and
retained integrability hypotheses can all be checked against the formulas
in this docstring and the cited Mathlib characterization of `𝓕`.
-/

open MeasureTheory
open scoped FourierTransform

@[expose] public section

namespace ControlTheory

/-- The Fourier transform in angular frequency `ω`: `∫ t, e^{-iωt} * f t`.
Mathlib's `𝓕` uses frequency in hertz (`e^{-2πitξ}`), so the angular form at
`ω` is the hertz form at `ω / (2π)`; see `fourierAngular_eq`. -/
noncomputable def fourierAngular (f : ℝ → ℂ) (ω : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (↑(-(ω * t)) * Complex.I) * f t

set_option linter.unusedVariables false in
/-- Angular/hertz agreement (roadmap leaf `SSC-U07.T01`, clauses
`SSC-F02.c02.b`, `SSC-U07.c01`): for integrable `f`, the angular-frequency
transform at `ω` is Mathlib's hertz transform `𝓕` at `ω / (2π)`. -/
theorem fourierAngular_eq {f : ℝ → ℂ} (hf : Integrable f) (ω : ℝ) :
    fourierAngular f ω = 𝓕 f (ω / (2 * Real.pi)) := by
  unfold fourierAngular
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with t
  have hexp : (-2 * Real.pi * t * (ω / (2 * Real.pi))) = (-(ω * t)) := by
    have h2pi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    field_simp
  rw [hexp]

set_option linter.unusedVariables false in
/-- Conjugate symmetry in the hertz convention: for a real-valued integrable
`f` (viewed in `ℂ`), `𝓕 f (-ξ) = conj (𝓕 f ξ)`. -/
theorem fourier_neg_eq_conj_of_real {f : ℝ → ℝ}
    (hf : Integrable (fun t => ((f t : ℝ) : ℂ))) (ξ : ℝ) :
    𝓕 (fun t => ((f t : ℝ) : ℂ)) (-ξ) = starRingEnd ℂ (𝓕 (fun t => ((f t : ℝ) : ℂ)) ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  have hI : ((↑(-2 * Real.pi * t * (-ξ)) : ℂ) * Complex.I) =
      ((↑(-2 * Real.pi * t * ξ) : ℂ) * (-Complex.I)) := by
    push_cast
    ring
  simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
  rw [hI]

set_option linter.unusedVariables false in
/-- Time-shift phase rule in the hertz convention: delaying by `a` multiplies
the transform by `e^{-2πiaξ}`. -/
theorem fourier_shift {f : ℝ → ℂ} (hf : Integrable f) (a ξ : ℝ) :
    𝓕 (fun t => f (t - a)) ξ =
      Complex.exp (↑(-2 * Real.pi * a * ξ) * Complex.I) * 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have hexp : ∀ t : ℝ, Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) =
      Complex.exp ((↑(-2 * Real.pi * a * ξ) : ℂ) * Complex.I) *
        Complex.exp ((↑(-2 * Real.pi * (t - a) * ξ) : ℂ) * Complex.I) := by
    intro t
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcongr : (fun t : ℝ => Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * f (t - a)) =ᵐ[volume]
      (fun t : ℝ => Complex.exp ((↑(-2 * Real.pi * a * ξ) : ℂ) * Complex.I) *
        (Complex.exp ((↑(-2 * Real.pi * (t - a) * ξ) : ℂ) * Complex.I) * f (t - a))) := by
    filter_upwards with t
    rw [hexp t]
    exact mul_assoc _ _ _
  rw [integral_congr_ae hcongr, integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self
    (fun u => Complex.exp ((↑(-2 * Real.pi * u * ξ) : ℂ) * Complex.I) * f u) a

set_option linter.unusedVariables false in
/-- Modulation phase rule in the hertz convention: multiplying by
`e^{2πiat}` shifts the transform argument by `a`. -/
theorem fourier_modulation {f : ℝ → ℂ} (hf : Integrable f) (a ξ : ℝ) :
    𝓕 (fun t => Complex.exp (↑(2 * Real.pi * a * t) * Complex.I) * f t) ξ =
      𝓕 f (ξ - a) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with t
  have hreal : (-2 * Real.pi * t * ξ) + (2 * Real.pi * a * t) =
      (-2 * Real.pi * t * (ξ - a)) := by ring
  have hexp : Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) *
        Complex.exp ((↑(2 * Real.pi * a * t) : ℂ) * Complex.I) =
      Complex.exp ((↑(-2 * Real.pi * t * (ξ - a)) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    rw [← add_mul, ← Complex.ofReal_add, hreal]
  rw [← mul_assoc, hexp]

/-- Time-shift phase rule in the angular convention: delaying by `a`
multiplies `fourierAngular` by `e^{-iaω}`. -/
theorem fourierAngular_shift {f : ℝ → ℂ} (hf : Integrable f) (a ω : ℝ) :
    fourierAngular (fun t => f (t - a)) ω =
      Complex.exp (↑(-(a * ω)) * Complex.I) * fourierAngular f ω := by
  have hfshift : Integrable (fun t : ℝ => f (t - a)) := hf.comp_sub_right a
  rw [fourierAngular_eq hfshift ω, fourierAngular_eq hf ω,
    fourier_shift hf a (ω / (2 * Real.pi))]
  have hexp : (-2 * Real.pi * a * (ω / (2 * Real.pi))) = (-(a * ω)) := by
    have h2pi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    field_simp
  rw [hexp]

end ControlTheory
