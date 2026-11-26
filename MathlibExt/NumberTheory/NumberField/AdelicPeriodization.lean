/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.lean`
and
`P2M/Sol/S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import MathlibExt.NumberTheory.NumberField.AdelicBox
import Mathlib.LinearAlgebra.Countable

/-!
# Periodization over the adelic fundamental box

For a number field `F`, the box `NumberField.AdelicBox.adelicBox F` is a fundamental domain for
the translation action of the principal adeles `F ⊆ 𝔸_F`. This file records the unfolding
identities for a translation-invariant measure `μ` on `𝔸_F`, for instance an additive Haar
measure: summing the integrals over the box of all rational translates of a function recovers
its integral over the adeles, and for an integrable function the periodized function
`t ↦ ∑' ξ : F, Φ (t + ξ)` is integrable on the box with the same integral.

## Main statements

* `NumberField.AdelicPeriodization.tsum_setLIntegral_adelicBox_comp_add`
* `NumberField.AdelicPeriodization.tsum_setIntegral_adelicBox_comp_add`
* `NumberField.AdelicPeriodization.integrableOn_adelicBox_tsum_comp_add`
* `NumberField.AdelicPeriodization.setIntegral_adelicBox_tsum_comp_add`
-/

@[expose] public section

noncomputable section

open MeasureTheory NumberField NumberField.AdelicBox Filter
open scoped ENNReal

namespace NumberField.AdelicPeriodization

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

variable (F : Type*) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

/-- **The number field as the principal adeles.** For a number field `F`, the identification of
`F` with the principal subgroup of its adele ring `𝔸_F`, sending `k` to the principal adele
`k`. -/
def principalEquiv : F ≃ AdeleRing.principalSubgroup (𝓞 F) F :=
  Equiv.ofBijective (fun k => ⟨ι k, k, rfl⟩)
    ⟨fun _ _ h => AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h), by
      rintro ⟨_, k, rfl⟩; exact ⟨k, rfl⟩⟩

@[simp]
theorem coe_principalEquiv_apply (k : F) : (principalEquiv F k : 𝔸) = ι k := rfl

private theorem countable_principalSubgroup :
    Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  have : Countable F := Countable.of_moduleFinite (R := ℚ)
  exact (principalEquiv F).symm.injective.countable

/-- **Unfolding over the adelic box, nonnegative functions.** Let `F` be a number field and `μ`
a translation-invariant measure on its adele ring `𝔸_F`. For every `f : 𝔸_F → ℝ≥0∞`, the sum
over `ξ ∈ F` of the lower Lebesgue integrals of `t ↦ f (t + ξ)` over the adelic box
`adelicBox F` is the lower Lebesgue integral of `f` over `𝔸_F`. -/
theorem tsum_setLIntegral_adelicBox_comp_add (μ : Measure 𝔸) [μ.IsAddLeftInvariant]
    (f : 𝔸 → ℝ≥0∞) :
    ∑' ξ : F, ∫⁻ t in adelicBox F, f (t + ι ξ) ∂μ = ∫⁻ t, f t ∂μ := by
  have := countable_principalSubgroup F
  rw [(isAddFundamentalDomain_adelicBox F μ).lintegral_eq_tsum'' f,
    ← (principalEquiv F).tsum_eq]
  refine tsum_congr fun ξ => lintegral_congr fun t => ?_
  change f (t + ι ξ) = f (ι ξ + t)
  rw [add_comm]

/-- **Unfolding over the adelic box, integrable functions.** Let `F` be a number field and `μ` a
translation-invariant measure on its adele ring `𝔸_F`. For an integrable `Φ : 𝔸_F → ℂ`, the sum
over `ξ ∈ F` of the integrals of `t ↦ Φ (t + ξ)` over the adelic box `adelicBox F` is the
integral of `Φ` over `𝔸_F`. -/
theorem tsum_setIntegral_adelicBox_comp_add (μ : Measure 𝔸) [μ.IsAddLeftInvariant]
    {Φ : 𝔸 → ℂ} (hΦ : Integrable Φ μ) :
    ∑' ξ : F, ∫ t in adelicBox F, Φ (t + ι ξ) ∂μ = ∫ t, Φ t ∂μ := by
  have := countable_principalSubgroup F
  rw [(isAddFundamentalDomain_adelicBox F μ).integral_eq_tsum'' Φ hΦ,
    ← (principalEquiv F).tsum_eq]
  refine tsum_congr fun ξ => integral_congr_ae (Eventually.of_forall fun t => ?_)
  change Φ (t + ι ξ) = Φ (ι ξ + t)
  rw [add_comm]

/-- **The periodization is integrable on the adelic box.** Let `F` be a number field and `μ` a
translation-invariant measure on its adele ring `𝔸_F`. For an integrable `Φ : 𝔸_F → ℂ`, the
periodized function `t ↦ ∑' ξ : F, Φ (t + ξ)` is integrable on the adelic box `adelicBox F`. -/
theorem integrableOn_adelicBox_tsum_comp_add (μ : Measure 𝔸) [μ.IsAddLeftInvariant]
    {Φ : 𝔸 → ℂ} (hΦ : Integrable Φ μ) :
    IntegrableOn (fun t => ∑' ξ : F, Φ (t + ι ξ)) (adelicBox F) μ := by
  have : Countable F := Countable.of_moduleFinite (R := ℚ)
  set ν : Measure 𝔸 := μ.restrict (adelicBox F) with hν
  have hmeas : ∀ ξ : F, AEStronglyMeasurable (fun t => Φ (t + ι ξ)) ν :=
    fun ξ => (hΦ.comp_add_right (ι ξ)).aestronglyMeasurable.restrict
  have hgmeas : AEMeasurable (fun t => ∑' ξ : F, ‖Φ (t + ι ξ)‖ₑ) ν := by
    simp_rw [tsum_eq_iSup_sum]
    exact AEMeasurable.iSup fun s =>
      Finset.aemeasurable_fun_sum s fun ξ _ => (hmeas ξ).eNorm
  have hglint : ∫⁻ t, (∑' ξ : F, ‖Φ (t + ι ξ)‖ₑ) ∂ν < ∞ := by
    rw [lintegral_tsum fun ξ => (hmeas ξ).eNorm, hν,
      tsum_setLIntegral_adelicBox_comp_add F μ (fun t => ‖Φ t‖ₑ)]
    exact hΦ.2
  have hgint : Integrable (fun t => ∑' ξ : F, ‖Φ (t + ι ξ)‖ₑ) ν :=
    ⟨hgmeas.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_eNorm]
      simpa only [eNorm_eq_self] using hglint⟩
  have hae : ∀ᵐ t ∂ν, HasSum (fun ξ : F => Φ (t + ι ξ))
      (∑' ξ : F, Φ (t + ι ξ)) := by
    filter_upwards [ae_lt_top' hgmeas hglint.ne] with t ht
    have hs : Summable fun ξ : F => (‖Φ (t + ι ξ)‖₊ : ℝ) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
      simpa only [eNorm_eq_nnNorm] using ht.ne
    exact (Summable.of_norm (by simpa only [coe_nnNorm] using hs)).hasSum
  have hPmeas : AEStronglyMeasurable (fun t => ∑' ξ : F, Φ (t + ι ξ)) ν :=
    aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset F))
      (f := fun s : Finset F => fun t => ∑ ξ ∈ s, Φ (t + ι ξ))
      (fun s => Finset.aestronglyMeasurable_fun_sum s fun ξ _ => hmeas ξ) hae
  exact hgint.mono'_eNorm hPmeas (Eventually.of_forall fun t => eNorm_tsum_le_tsum_eNorm)

/-- **Periodization over the adelic box commutes with integration.** Let `F` be a number field
and `μ` a translation-invariant measure on its adele ring `𝔸_F`. For an integrable
`Φ : 𝔸_F → ℂ`, the integral over the adelic box `adelicBox F` of the periodized function
`t ↦ ∑' ξ : F, Φ (t + ξ)` is the integral of `Φ` over `𝔸_F`. -/
theorem setIntegral_adelicBox_tsum_comp_add (μ : Measure 𝔸) [μ.IsAddLeftInvariant]
    {Φ : 𝔸 → ℂ} (hΦ : Integrable Φ μ) :
    ∫ t in adelicBox F, (∑' ξ : F, Φ (t + ι ξ)) ∂μ = ∫ t, Φ t ∂μ := by
  have : Countable F := Countable.of_moduleFinite (R := ℚ)
  have hmeas : ∀ ξ : F,
      AEStronglyMeasurable (fun t => Φ (t + ι ξ)) (μ.restrict (adelicBox F)) :=
    fun ξ => (hΦ.comp_add_right (ι ξ)).aestronglyMeasurable.restrict
  have hfin : ∑' ξ : F, ∫⁻ t in adelicBox F, ‖Φ (t + ι ξ)‖ₑ ∂μ ≠ ∞ := by
    rw [tsum_setLIntegral_adelicBox_comp_add F μ (fun t => ‖Φ t‖ₑ)]
    exact hΦ.2.ne
  rw [integral_tsum hmeas hfin, tsum_setIntegral_adelicBox_comp_add F μ hΦ]

end NumberField.AdelicPeriodization

end
