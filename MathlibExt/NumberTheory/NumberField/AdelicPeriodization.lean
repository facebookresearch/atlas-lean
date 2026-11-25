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
identities: summing the integrals over the box of all rational translates of a function recovers
its integral over the adeles, and for an integrable function the periodized function
`t ↦ ∑' ξ : F, Φ (t + ξ)` is integrable on the box with the same integral.

## Main statements

* `NumberField.AdelicPeriodization.tsum_lintegral_adelicBox_comp_add`
* `NumberField.AdelicPeriodization.tsum_integral_adelicBox_comp_add`
* `NumberField.AdelicPeriodization.integrableOn_and_setIntegral_tsum_translate`
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

/-- The adele ring of a number field is nontrivial. -/
instance nontrivial_adeleRing : Nontrivial 𝔸 := by
  have : Inhabited (InfinitePlace F) := Classical.inhabited_of_nonempty inferInstance
  have : Nontrivial (InfiniteAdeleRing F) :=
    inferInstanceAs (Nontrivial ((w : InfinitePlace F) → w.Completion))
  exact inferInstanceAs
    (Nontrivial (InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))

/-- The identification of the number field with the principal subgroup of the
adele ring. -/
def principalEquiv : F ≃ AdeleRing.principalSubgroup (𝓞 F) F :=
  Equiv.ofBijective (fun k => ⟨ι k, k, rfl⟩)
    ⟨fun a b h => (algebraMap F 𝔸).injective (congrArg Subtype.val h), by
      rintro ⟨_, k, rfl⟩; exact ⟨k, rfl⟩⟩

@[simp]
theorem coe_principalEquiv_apply (k : F) : (principalEquiv F k : 𝔸) = ι k := rfl

private theorem countable_principalSubgroup :
    Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  have : Countable F := Countable.of_moduleFinite (R := ℚ)
  exact (principalEquiv F).symm.injective.countable

/-- Unfolding for nonnegative functions: the sum over rational translates of the
lower integrals over the adelic box is the lower integral over the adeles. -/
theorem tsum_lintegral_adelicBox_comp_add (μ : Measure 𝔸) [μ.IsAddHaarMeasure]
    (f : 𝔸 → ℝ≥0∞) :
    ∑' ξ : F, ∫⁻ t in adelicBox F, f (t + ι ξ) ∂μ = ∫⁻ t, f t ∂μ := by
  have := countable_principalSubgroup F
  rw [(isAddFundamentalDomain_adelicBox F μ).lintegral_eq_tsum'' f,
    ← (principalEquiv F).tsum_eq]
  refine tsum_congr fun ξ => lintegral_congr fun t => ?_
  show f (t + ι ξ) = f (ι ξ + t)
  rw [add_comm]

/-- Unfolding for integrable functions: the sum over rational translates of the
integrals over the adelic box is the integral over the adeles. -/
theorem tsum_integral_adelicBox_comp_add (μ : Measure 𝔸) [μ.IsAddHaarMeasure]
    {Φ : 𝔸 → ℂ} (hΦ : Integrable Φ μ) :
    ∑' ξ : F, ∫ t in adelicBox F, Φ (t + ι ξ) ∂μ = ∫ t, Φ t ∂μ := by
  have := countable_principalSubgroup F
  rw [(isAddFundamentalDomain_adelicBox F μ).integral_eq_tsum'' Φ hΦ,
    ← (principalEquiv F).tsum_eq]
  refine tsum_congr fun ξ => integral_congr_ae (Eventually.of_forall fun t => ?_)
  show Φ (t + ι ξ) = Φ (ι ξ + t)
  rw [add_comm]

/-- Periodization over the adelic fundamental box commutes with integration:
for an integrable function on the adeles, the periodized sum over rational
translates is integrable on the box, and its integral over the box equals the
global integral. -/
theorem integrableOn_and_setIntegral_tsum_translate (μ : Measure 𝔸) [μ.IsAddHaarMeasure]
    {Φ : 𝔸 → ℂ}
    (hΦ : Integrable Φ μ) :
    IntegrableOn (fun t => ∑' ξ : F, Φ (t + ι ξ)) (adelicBox F) μ ∧
      ∫ t in adelicBox F, (∑' ξ : F, Φ (t + ι ξ)) ∂μ = ∫ t, Φ t ∂μ := by
  have := countable_principalSubgroup F
  have : Countable F := Countable.of_moduleFinite (R := ℚ)
  set ν : Measure 𝔸 := μ.restrict (adelicBox F) with hν
  have hT : ∀ ξ : F, Integrable (fun t => Φ (t + ι ξ)) μ :=
    fun ξ => hΦ.comp_add_right (ι ξ)
  have hmeas : ∀ ξ : F, AEStronglyMeasurable (fun t => Φ (t + ι ξ)) ν :=
    fun ξ => (hT ξ).aestronglyMeasurable.restrict
  have hgmeas : AEMeasurable (fun t => ∑' ξ : F, ‖Φ (t + ι ξ)‖ₑ) ν := by
    simp_rw [tsum_eq_iSup_sum]
    exact AEMeasurable.iSup fun s =>
      Finset.aemeasurable_fun_sum s fun ξ _ => (hmeas ξ).eNorm
  have hsum : ∑' ξ : F, ∫⁻ t, ‖Φ (t + ι ξ)‖ₑ ∂ν = ∫⁻ t, ‖Φ t‖ₑ ∂μ := by
    rw [hν, tsum_lintegral_adelicBox_comp_add F μ (fun t => ‖Φ t‖ₑ)]
  have hglint : ∫⁻ t, (∑' ξ : F, ‖Φ (t + ι ξ)‖ₑ) ∂ν < ∞ := by
    rw [lintegral_tsum fun ξ => (hmeas ξ).eNorm, hsum]
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
  refine ⟨hgint.mono'_eNorm hPmeas
    (Eventually.of_forall fun t => eNorm_tsum_le_tsum_eNorm), ?_⟩
  have hfin : ∑' ξ : F, ∫⁻ t, ‖Φ (t + ι ξ)‖ₑ ∂ν ≠ ∞ := by
    rw [hsum]; exact hΦ.2.ne
  show ∫ t, (∑' ξ : F, Φ (t + ι ξ)) ∂ν = ∫ t, Φ t ∂μ
  rw [integral_tsum hmeas hfin, hν, tsum_integral_adelicBox_comp_add F μ hΦ]

end NumberField.AdelicPeriodization

end
