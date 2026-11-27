/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdelicPeriodization

@[expose] public section

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicPeriodization
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

universe u

/-- Consumer with the original binders and conclusion: the field in `Type`, a Haar measure, and
the conjunction of integrability on the box and the integral identity. -/
private theorem exactSource (F : Type) [Field F] [NumberField F]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {Φ : AdeleRing (𝓞 F) F → ℂ} (hΦ : Integrable Φ μ) :
    IntegrableOn (fun t => ∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ))
        (adelicBox F) μ ∧
      ∫ t in adelicBox F, (∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ)) ∂μ
        = ∫ t, Φ t ∂μ :=
  ⟨integrableOn_adelicBox_tsum_comp_add F μ hΦ, setIntegral_adelicBox_tsum_comp_add F μ hΦ⟩

/-- The integral identity at an arbitrary universe level. -/
example (F : Type u) [Field F] [NumberField F] (μ : Measure (AdeleRing (𝓞 F) F))
    [μ.IsAddHaarMeasure] {Φ : AdeleRing (𝓞 F) F → ℂ} (hΦ : Integrable Φ μ) :
    ∫ t in adelicBox F, (∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ)) ∂μ
      = ∫ t, Φ t ∂μ :=
  setIntegral_adelicBox_tsum_comp_add F μ hΦ

/-- The summed-integral form, with the original binders. -/
example (F : Type) [Field F] [NumberField F]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {Φ : AdeleRing (𝓞 F) F → ℂ} (hΦ : Integrable Φ μ) :
    ∑' ξ : F, ∫ t in adelicBox F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ) ∂μ
      = ∫ t, Φ t ∂μ :=
  tsum_setIntegral_adelicBox_comp_add F μ hΦ

/-- For nonnegative functions no integrability is needed: with `f = 1`, the box
translates tile the adeles, so the box measures sum to the total measure. -/
example (F : Type*) [Field F] [NumberField F] (μ : Measure (AdeleRing (𝓞 F) F))
    [μ.IsAddHaarMeasure] :
    ∑' _ξ : F, μ (adelicBox F) = μ Set.univ := by
  have h := tsum_setLIntegral_adelicBox_comp_add F μ (fun _ => 1)
  simpa using h

/-- Only translation invariance is used: all four statements apply to a translation-invariant
measure that is not assumed to be a Haar measure. -/
example (F : Type*) [Field F] [NumberField F] (μ : Measure (AdeleRing (𝓞 F) F))
    [μ.IsAddLeftInvariant] (f : AdeleRing (𝓞 F) F → ℝ≥0∞) {Φ : AdeleRing (𝓞 F) F → ℂ}
    (hΦ : Integrable Φ μ) :
    (∑' ξ : F, ∫⁻ t in adelicBox F, f (t + algebraMap F (AdeleRing (𝓞 F) F) ξ) ∂μ
        = ∫⁻ t, f t ∂μ) ∧
      (∑' ξ : F, ∫ t in adelicBox F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ) ∂μ
        = ∫ t, Φ t ∂μ) ∧
      IntegrableOn (fun t => ∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ))
        (adelicBox F) μ ∧
      ∫ t in adelicBox F, (∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ)) ∂μ
        = ∫ t, Φ t ∂μ :=
  ⟨tsum_setLIntegral_adelicBox_comp_add F μ f, tsum_setIntegral_adelicBox_comp_add F μ hΦ,
    integrableOn_adelicBox_tsum_comp_add F μ hΦ, setIntegral_adelicBox_tsum_comp_add F μ hΦ⟩

/-- A concrete instance over `ℚ` with the Haar measure `adelicAddHaar`: the box translates tile
the adeles, the box has positive measure and `ℚ` is infinite, so the adeles have infinite
measure. -/
example : NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ Set.univ = ∞ := by
  have := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  have h := tsum_setLIntegral_adelicBox_comp_add ℚ
    (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (fun _ => 1)
  simp only [lintegral_one, Measure.restrict_apply_univ] at h
  rw [← h]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (adelicAddHaar_adelicBox_pos ℚ).ne'

/-- `principalEquiv` sends `k` to the principal adele `k`. -/
example (F : Type*) [Field F] [NumberField F] (k : F) :
    (principalEquiv F).symm ⟨algebraMap F (AdeleRing (𝓞 F) F) k, k, rfl⟩ = k :=
  (principalEquiv F).symm_apply_eq.mpr rfl
