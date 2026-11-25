/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Width monotonicity of Lorentzian integrals

For a finite measure `μ` on `ℝ` (nonnegative by type, the zero measure included) and a width
`Γ > 0`, let `F Γ = ∫ E, Γ ^ 2 / (E ^ 2 + Γ ^ 2) ∂μ`. The Lorentzian kernel takes values in
`(0, 1]`, equals `1` at `E = 0` for every width, and increases strictly with `Γ` at every
`E ≠ 0`. Hence `F` is nondecreasing in the width, and it increases strictly between two widths
exactly when `μ` puts positive mass off the origin. If all of the mass sits at the origin,
`F Γ = μ {0}` for every `Γ > 0`.

The two widths are compared against the same fixed measure. Neither a zero width nor a signed
or infinite measure is covered here.

## Main declarations

* `integral_lorentzian_mono`: `F Γ₁ ≤ F Γ₂` for `0 < Γ₁ ≤ Γ₂`.
* `integral_lorentzian_lt_iff`: for `0 < Γ₁ < Γ₂`, `F Γ₁ < F Γ₂` if and only if
  `0 < μ {0}ᶜ`.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.MeasureTheory.Integral.LorentzianWidth


private lemma lorentzian_pos {Γ : ℝ} (hΓ : 0 < Γ) (E : ℝ) : 0 < Γ ^ 2 / (E ^ 2 + Γ ^ 2) := by
  positivity

private lemma lorentzian_le_one {Γ : ℝ} (hΓ : 0 < Γ) (E : ℝ) : Γ ^ 2 / (E ^ 2 + Γ ^ 2) ≤ 1 := by
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg E]

private lemma integrable_lorentzian (μ : Measure ℝ) [IsFiniteMeasure μ] {Γ : ℝ} (hΓ : 0 < Γ) :
    Integrable (fun E : ℝ => Γ ^ 2 / (E ^ 2 + Γ ^ 2)) μ := by
  have hc : Continuous (fun E : ℝ => Γ ^ 2 / (E ^ 2 + Γ ^ 2)) :=
    continuous_const.div (by fun_prop) (fun E => by positivity)
  refine (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable (ae_of_all _ fun E => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (lorentzian_pos hΓ E)]
  exact lorentzian_le_one hΓ E

private lemma lorentzian_le {Γ₁ Γ₂ : ℝ} (hΓ₁ : 0 < Γ₁) (hΓ : Γ₁ ≤ Γ₂) (E : ℝ) :
    Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2) ≤ Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2) := by
  have hΓ₂ : 0 < Γ₂ := hΓ₁.trans_le hΓ
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : Γ₁ ^ 2 ≤ Γ₂ ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg E)]

private lemma lorentzian_at_zero {Γ : ℝ} (hΓ : 0 < Γ) :
    Γ ^ 2 / ((0 : ℝ) ^ 2 + Γ ^ 2) = 1 := by
  rw [zero_pow two_ne_zero, zero_add, div_self (pow_ne_zero 2 hΓ.ne')]

private lemma lorentzian_sub_pos_iff {Γ₁ Γ₂ : ℝ} (hΓ₁ : 0 < Γ₁) (hΓ : Γ₁ < Γ₂) (E : ℝ) :
    0 < Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2) - Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2) ↔ E ≠ 0 := by
  have hΓ₂ : 0 < Γ₂ := hΓ₁.trans hΓ
  rw [sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor
  · rintro h rfl
    nlinarith
  · intro hE
    have hE2 : 0 < E ^ 2 := by positivity
    have hsq : Γ₁ ^ 2 < Γ₂ ^ 2 := by nlinarith
    nlinarith

/-- **Lorentzian integrals are nondecreasing in the width.** Let `μ` be a finite measure on
`ℝ`; it is nonnegative by type and may be the zero measure. If `0 < Γ₁ ≤ Γ₂`, then
`∫ E, Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2) ∂μ ≤ ∫ E, Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2) ∂μ`. Both widths are
integrated against the same measure, and equal widths are allowed. -/
theorem integral_lorentzian_mono
    (μ : Measure ℝ) [IsFiniteMeasure μ] {Γ₁ Γ₂ : ℝ}
    (hΓ₁ : 0 < Γ₁) (hΓ : Γ₁ ≤ Γ₂) :
    (∫ E, Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2) ∂μ) ≤
      (∫ E, Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2) ∂μ) :=
  integral_mono (integrable_lorentzian μ hΓ₁) (integrable_lorentzian μ (hΓ₁.trans_le hΓ))
    (fun E => lorentzian_le hΓ₁ hΓ E)

/-- **Strict width monotonicity of Lorentzian integrals.** Let `μ` be a finite measure on `ℝ`
(the zero measure included) and `0 < Γ₁ < Γ₂`. Then
`∫ E, Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2) ∂μ < ∫ E, Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2) ∂μ` if and only if `μ`
gives positive mass to `{0}ᶜ`. The kernel equals `1` at `E = 0` for every width, so mass at the
origin never contributes to the increase; in particular the zero measure, and any multiple of the
Dirac mass at `0`, give equal integrals. -/
theorem integral_lorentzian_lt_iff
    (μ : Measure ℝ) [IsFiniteMeasure μ] {Γ₁ Γ₂ : ℝ}
    (hΓ₁ : 0 < Γ₁) (hΓ : Γ₁ < Γ₂) :
    ((∫ E, Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2) ∂μ) <
      (∫ E, Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2) ∂μ)) ↔
      0 < μ ({(0 : ℝ)}ᶜ) := by
  have hΓ₂ : 0 < Γ₂ := hΓ₁.trans hΓ
  have hi₁ := integrable_lorentzian μ hΓ₁
  have hi₂ := integrable_lorentzian μ hΓ₂
  have hnn : 0 ≤ fun E : ℝ => Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2) - Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2) :=
    fun E => sub_nonneg.mpr (lorentzian_le hΓ₁ hΓ.le E)
  have hsupp : Function.support
      (fun E : ℝ => Γ₂ ^ 2 / (E ^ 2 + Γ₂ ^ 2) - Γ₁ ^ 2 / (E ^ 2 + Γ₁ ^ 2)) = {(0 : ℝ)}ᶜ := by
    ext E
    simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro h rfl
      exact h (by rw [lorentzian_at_zero hΓ₁, lorentzian_at_zero hΓ₂, sub_self])
    · intro hE
      exact ((lorentzian_sub_pos_iff hΓ₁ hΓ E).mpr hE).ne'
  rw [← sub_pos, ← integral_sub hi₂ hi₁,
    integral_pos_iff_support_of_nonneg hnn (hi₂.sub hi₁), hsupp]

end MathlibExt.MeasureTheory.Integral.LorentzianWidth
