/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.VerticalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Tests for principal-value integrals along a vertical line

Non-vacuity of `Complex.HasVerticalIntegral`: it holds with the expected value for the
absolutely integrable `(1 + (im s)²)⁻¹`, fails for the constant `1`, and (boundary probe) holds
with value `0` for the positive, non-locally-integrable `|im s|⁻¹`, because interval integrals of
non-integrable functions are `0`.
-/

@[expose] public section

open Filter MeasureTheory Complex
open scoped Real Topology

/-- The Cauchy density on a vertical line, as a function of `s`. -/
private noncomputable def cauchyLine (s : ℂ) : ℂ := (((1 + s.im ^ 2)⁻¹ : ℝ) : ℂ)

@[simp] private lemma cauchyLine_def (s : ℂ) :
    cauchyLine s = (((1 + s.im ^ 2)⁻¹ : ℝ) : ℂ) := rfl

private lemma cauchyLine_apply (c t : ℝ) :
    cauchyLine (c + t * I) = (((1 + t ^ 2)⁻¹ : ℝ) : ℂ) := by
  simp

private lemma integrable_cauchy : Integrable fun t : ℝ => (((1 + t ^ 2)⁻¹ : ℝ) : ℂ) :=
  integrable_inv_one_add_sq.ofReal

private lemma hasVerticalIntegral_cauchyLine (c : ℝ) :
    HasVerticalIntegral c cauchyLine (1 / 2) := by
  have h := hasVerticalIntegral_of_integrable (c := c) (f := cauchyLine) integrable_cauchy
    (cauchyLine_apply c)
  convert h using 1
  rw [integral_complex_ofReal, integral_univ_inv_one_add_sq, Complex.real_smul]
  push_cast
  field_simp

/-- **Integrable example.** `(1 / 2π) ∫ (1 + t²)⁻¹ dt = 1 / 2`. -/
example : HasVerticalIntegral 3 cauchyLine (1 / 2) :=
  hasVerticalIntegral_cauchyLine 3

/-- `verticalIntegral` computes the value. -/
example : verticalIntegral (-1) cauchyLine = 1 / 2 :=
  (hasVerticalIntegral_cauchyLine _).verticalIntegral_eq

/-- Uniqueness rules out any other value. -/
example : ¬ HasVerticalIntegral 0 cauchyLine 1 := fun h =>
  absurd ((hasVerticalIntegral_cauchyLine 0).unique h) (by norm_num)

/-- `VerticalIntegrable.hasVerticalIntegral` agrees with the closed form. -/
example : HasVerticalIntegral 0 cauchyLine ((1 / (2 * π)) • ∫ t : ℝ, cauchyLine (0 + t * I)) :=
  VerticalIntegrable.hasVerticalIntegral (by
    simpa [VerticalIntegrable, cauchyLine_apply] using integrable_cauchy)

/-- Zero function. -/
example : HasVerticalIntegral 5 (fun _ : ℂ => (0 : ℂ)) 0 := hasVerticalIntegral_zero

/-- Linearity, with the segment-integrability side conditions. -/
example : HasVerticalIntegral 0 (fun s => cauchyLine s + 2 * cauchyLine s) (1 / 2 + 2 * (1 / 2)) :=
  (hasVerticalIntegral_cauchyLine 0).add ((hasVerticalIntegral_cauchyLine 0).const_mul 2)
    (fun R => by simpa [cauchyLine_apply] using integrable_cauchy.intervalIntegrable)
    (fun R => by
      simpa [cauchyLine_apply] using (integrable_cauchy.const_mul 2).intervalIntegrable)

example : HasVerticalIntegral 0 (fun s => -cauchyLine s) (-(1 / 2)) :=
  (hasVerticalIntegral_cauchyLine 0).neg

/-- Only the values on the line matter: `cauchyLine` and a function equal to it on `re s = 0`. -/
example : HasVerticalIntegral 0
    (fun s => if s.re = 0 then cauchyLine s else 37) (1 / 2) :=
  (hasVerticalIntegral_cauchyLine 0).congr_line fun t => by simp

/-- Translation of the abscissa. -/
example : HasVerticalIntegral 2 (fun s => cauchyLine (s - (5 : ℝ))) (1 / 2) :=
  (hasVerticalIntegral_cauchyLine (2 - 5)).comp_sub_ofReal

/-- The truncation bound: `‖v - truncation at T‖ ≤ 1 / (π T)`. -/
example {T : ℝ} (hT : 1 ≤ T) :
    ‖(1 / 2 : ℂ) - (1 / (2 * π)) • ∫ t in (-T)..T, cauchyLine (0 + t * I)‖ ≤ 1 / (π * T) := by
  refine (hasVerticalIntegral_cauchyLine 0).norm_sub_le_of_norm_le_div_sq
    (fun R => by simpa [cauchyLine_apply] using integrable_cauchy.intervalIntegrable)
    (fun t ht => ?_) hT
  rw [cauchyLine_apply, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have ht2 : 0 < t ^ 2 := by
    have : (1 : ℝ) ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    linarith
  rw [one_div]
  exact inv_anti₀ ht2 (by linarith)

/-! ### Non-examples -/

/-- **Non-example.** The constant `1` has no principal value: the truncations are `R / π`. -/
example (c : ℝ) (v : ℂ) : ¬ HasVerticalIntegral c (fun _ => (1 : ℂ)) v := by
  intro h
  have hn := h.norm
  have hat : Tendsto (fun R : ℝ => ‖(1 / (2 * π)) • ∫ t in (-R)..R, (fun _ : ℂ => (1 : ℂ))
      (c + t * I)‖) atTop atTop := by
    refine (tendsto_id.atTop_div_const Real.pi_pos).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [intervalIntegral.integral_const, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, norm_one, abs_of_pos (by positivity), abs_of_nonneg (by linarith)]
    simp only [id]
    field_simp
    ring
  exact not_tendsto_nhds_of_tendsto_atTop hat _ hn

/-- `|t|⁻¹` is not interval integrable on any `[-R, R]` with `R ≠ 0`. -/
private lemma not_intervalIntegrable_abs_inv {R : ℝ} (hR : R ≠ 0) :
    ¬ IntervalIntegrable (fun t : ℝ => (((|t|⁻¹ : ℝ)) : ℂ)) volume (-R) R := by
  intro h
  have h' : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (-R) R := by
    refine h.norm.mono_fun (by fun_prop) (Eventually.of_forall fun t => ?_)
    simp
  rw [intervalIntegrable_inv_iff] at h'
  rcases h' with h' | h'
  · exact hR (by linarith)
  · exact h' (Set.mem_uIcc.mpr (by rcases le_or_gt 0 R with h | h <;> [left; right] <;>
      constructor <;> linarith))

/-- **Boundary probe (junk value).** The integrand `|im s|⁻¹` is positive and its integral over
every segment `[-R, R]` diverges to `+∞`, yet `HasVerticalIntegral 0` holds with value `0`: the
Bochner interval integral of a non-integrable function is `0`, so every truncation is `0`. -/
example : HasVerticalIntegral 0 (fun s : ℂ => (((|s.im|⁻¹ : ℝ)) : ℂ)) 0 := by
  unfold HasVerticalIntegral
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hni := not_intervalIntegrable_abs_inv (R := R) hR.ne'
  rw [intervalIntegral.integral_undef (by simpa using hni), smul_zero]

/-- The same junk value is what `verticalIntegral` returns. -/
example : verticalIntegral 0 (fun s : ℂ => (((|s.im|⁻¹ : ℝ)) : ℂ)) = 0 := by
  apply HasVerticalIntegral.verticalIntegral_eq
  unfold HasVerticalIntegral
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hni := not_intervalIntegrable_abs_inv (R := R) hR.ne'
  rw [intervalIntegral.integral_undef (by simpa using hni), smul_zero]
