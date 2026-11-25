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

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

universe u

/-- Consumer with the original binders: the field in `Type` and a Haar measure. -/
private theorem exactSource (F : Type) [Field F] [NumberField F]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {Φ : AdeleRing (𝓞 F) F → ℂ} (hΦ : Integrable Φ μ) :
    IntegrableOn (fun t => ∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ))
        (adelicBox F) μ ∧
      ∫ t in adelicBox F, (∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ)) ∂μ
        = ∫ t, Φ t ∂μ :=
  integrableOn_and_setIntegral_tsum_translate F μ hΦ

/-- The same statement at an arbitrary universe level. -/
example (F : Type u) [Field F] [NumberField F] (μ : Measure (AdeleRing (𝓞 F) F))
    [μ.IsAddHaarMeasure] {Φ : AdeleRing (𝓞 F) F → ℂ} (hΦ : Integrable Φ μ) :
    ∫ t in adelicBox F, (∑' ξ : F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ)) ∂μ
      = ∫ t, Φ t ∂μ :=
  (integrableOn_and_setIntegral_tsum_translate F μ hΦ).2

/-- The summed-integral form, with the original binders. -/
example (F : Type) [Field F] [NumberField F]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {Φ : AdeleRing (𝓞 F) F → ℂ} (hΦ : Integrable Φ μ) :
    ∑' ξ : F, ∫ t in adelicBox F, Φ (t + algebraMap F (AdeleRing (𝓞 F) F) ξ) ∂μ
      = ∫ t, Φ t ∂μ :=
  tsum_integral_adelicBox_comp_add F μ hΦ

/-- For nonnegative functions no integrability is needed: with `f = 1`, the box
translates tile the adeles, so the box measures sum to the total measure. -/
example (F : Type*) [Field F] [NumberField F] (μ : Measure (AdeleRing (𝓞 F) F))
    [μ.IsAddHaarMeasure] :
    ∑' _ξ : F, μ (adelicBox F) = μ Set.univ := by
  have h := tsum_lintegral_adelicBox_comp_add F μ (fun _ => 1)
  simpa using h
