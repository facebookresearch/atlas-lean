/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-! # Differential entropy of a Gaussian

The differential entropy of `N (0, v)` is `(1/2) log (2 π e v)`,
computed from the density integral. This is the Gaussian case of
roadmap package QCI-35 of the Atlas TCS canon roadmap.

Source: Cover and Thomas, Elements of Information Theory (2006),
Section 8.5.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open scoped Real

/-- Differential entropy of the centered Gaussian with variance
`v` (as an integral against Lebesgue measure of its density
times its log), stated for `v ≠ 0`. -/
noncomputable def gaussEntropy (v : ℝ≥0) : ℝ :=
  -∫ x : ℝ, gaussianPDFReal 0 v x * Real.log (gaussianPDFReal 0 v x)

private lemma vpos {v : ℝ≥0} (hv : v ≠ 0) : 0 < (v : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)

private lemma log_pdf {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal 0 v x)
      = -(Real.log (2 * Real.pi * (v : ℝ)) / 2) - x ^ 2 / (2 * (v : ℝ)) := by
  have hvR : 0 < (v : ℝ) := vpos hv
  have h2pv : 0 < 2 * Real.pi * (v : ℝ) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  have hsqrt_pos : 0 < √(2 * Real.pi * (v : ℝ)) := Real.sqrt_pos.mpr h2pv
  have hsqrt_ne : √(2 * Real.pi * (v : ℝ)) ≠ 0 := ne_of_gt hsqrt_pos
  have hinv_ne : (√(2 * Real.pi * (v : ℝ)))⁻¹ ≠ 0 := inv_ne_zero hsqrt_ne
  have hexp_ne : Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ))) ≠ 0 := Real.exp_ne_zero _
  have hpdf : gaussianPDFReal 0 v x
      = (√(2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ))) := rfl
  rw [hpdf, Real.log_mul hinv_ne hexp_ne, Real.log_inv, Real.log_sqrt h2pv.le,
    Real.log_exp]
  simp only [sub_zero]
  ring

private lemma integrable_sq_mul_pdf {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x : ℝ => x ^ 2 * gaussianPDFReal 0 v x) := by
  have hmem : MemLp id 2 (gaussianReal (0 : ℝ) v) :=
    memLp_id_gaussianReal' 2 (by simp)
  have hint : Integrable (fun x : ℝ => (id x) ^ 2) (gaussianReal (0 : ℝ) v) :=
    hmem.integrable_sq
  simp only [id_eq] at hint
  have hgauss : gaussianReal (0 : ℝ) v
      = volume.withDensity (gaussianPDF 0 v) :=
    gaussianReal_of_var_ne_zero 0 hv
  have hmeas : Measurable (gaussianPDF (0 : ℝ) v) := measurable_gaussianPDF 0 v
  have hlt := ae_of_all (volume : Measure ℝ)
    (p := fun x : ℝ => gaussianPDF (0 : ℝ) v x < (⊤ : ENNReal))
    (fun x : ℝ => gaussianPDF_lt_top)
  have hiff : Integrable (fun x : ℝ => x ^ 2)
        (volume.withDensity (gaussianPDF (0 : ℝ) v))
      ↔ Integrable (fun x : ℝ => x ^ 2 * (gaussianPDF (0 : ℝ) v x).toReal) volume :=
    integrable_withDensity_iff hmeas hlt
  rw [hgauss] at hint
  have hint2 := hiff.mp hint
  simpa [toReal_gaussianPDF] using hint2

private lemma integral_sq_mul_pdf {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, x ^ 2 * gaussianPDFReal 0 v x = (v : ℝ) := by
  have hmean : integral (gaussianReal (0 : ℝ) v) (fun x : ℝ => x) = 0 :=
    integral_id_gaussianReal
  have hvar : variance (fun x : ℝ => x) (gaussianReal (0 : ℝ) v) = (v : ℝ) :=
    variance_fun_id_gaussianReal
  have haemeas : AEMeasurable (fun x : ℝ => x) (gaussianReal (0 : ℝ) v) :=
    measurable_id'.aemeasurable
  have hvar_eq := variance_of_integral_eq_zero haemeas hmean
  have hgauss_int : integral (gaussianReal (0 : ℝ) v) (fun x : ℝ => x ^ 2)
      = (v : ℝ) := by
    rw [← hvar_eq, hvar]
  have htrans : integral (gaussianReal (0 : ℝ) v) (fun x : ℝ => x ^ 2)
      = integral volume (fun x : ℝ => gaussianPDFReal 0 v x • x ^ 2) :=
    integral_gaussianReal_eq_integral_smul hv
  rw [hgauss_int] at htrans
  have hsmul : (fun x : ℝ => gaussianPDFReal 0 v x • x ^ 2)
      = (fun x : ℝ => x ^ 2 * gaussianPDFReal 0 v x) := by
    ext x
    rw [smul_eq_mul, mul_comm]
  rw [hsmul] at htrans
  exact htrans.symm

/-- The differential entropy of `N (0, v)` is
`(1 / 2) log (2 π e v)`. -/
theorem gaussEntropy_eq {v : ℝ≥0} (hv : v ≠ 0) :
    gaussEntropy v = (1 / 2) * Real.log (2 * π * Real.exp 1 * (v : ℝ)) := by
  unfold gaussEntropy
  have hvR : 0 < (v : ℝ) := vpos hv
  have hvRne : (v : ℝ) ≠ 0 := ne_of_gt hvR
  have h2pv : 0 < 2 * Real.pi * (v : ℝ) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  have h2pv_ne : 2 * Real.pi * (v : ℝ) ≠ 0 := ne_of_gt h2pv
  have hfeq : ∀ x : ℝ, gaussianPDFReal 0 v x * Real.log (gaussianPDFReal 0 v x)
      = (-(Real.log (2 * Real.pi * (v : ℝ)) / 2)) * gaussianPDFReal 0 v x
        - (1 / (2 * (v : ℝ))) * (x ^ 2 * gaussianPDFReal 0 v x) := by
    intro x
    rw [log_pdf hv x]
    ring
  have hint_pdf : Integrable (gaussianPDFReal 0 v) := integrable_gaussianPDFReal 0 v
  have hint1 : Integrable
      (fun x : ℝ => (-(Real.log (2 * Real.pi * (v : ℝ)) / 2))
        * gaussianPDFReal 0 v x) :=
    hint_pdf.const_mul _
  have hint_sq := integrable_sq_mul_pdf hv
  have hint2 : Integrable
      (fun x : ℝ => (1 / (2 * (v : ℝ))) * (x ^ 2 * gaussianPDFReal 0 v x)) :=
    hint_sq.const_mul _
  have hmain : (∫ x, gaussianPDFReal 0 v x * Real.log (gaussianPDFReal 0 v x))
      = ∫ x, (-(Real.log (2 * Real.pi * (v : ℝ)) / 2)) * gaussianPDFReal 0 v x
        - (1 / (2 * (v : ℝ))) * (x ^ 2 * gaussianPDFReal 0 v x) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => hfeq x))
  have hsplit := integral_sub hint1 hint2
  rw [hmain, hsplit]
  have h1 : (∫ x, (-(Real.log (2 * Real.pi * (v : ℝ)) / 2))
        * gaussianPDFReal 0 v x)
      = (-(Real.log (2 * Real.pi * (v : ℝ)) / 2)) * 1 := by
    rw [integral_const_mul, integral_gaussianPDFReal_eq_one 0 hv]
  have h2 : (∫ x, (1 / (2 * (v : ℝ))) * (x ^ 2 * gaussianPDFReal 0 v x))
      = (1 / (2 * (v : ℝ))) * (v : ℝ) := by
    rw [integral_const_mul, integral_sq_mul_pdf hv]
  rw [h1, h2]
  have hfrac : (1 / (2 * (v : ℝ))) * (v : ℝ) = 1 / 2 := by
    field_simp
  rw [hfrac]
  have hlog : Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ))
      = Real.log (2 * Real.pi * (v : ℝ)) + 1 := by
    have hrewrite : 2 * Real.pi * Real.exp 1 * (v : ℝ)
        = (2 * Real.pi * (v : ℝ)) * Real.exp 1 := by ring
    rw [hrewrite, Real.log_mul h2pv_ne (Real.exp_ne_zero 1), Real.log_exp]
  show -(-(Real.log (2 * Real.pi * (v : ℝ)) / 2) * 1 - 1 / 2)
    = (1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ))
  rw [hlog]
  ring
