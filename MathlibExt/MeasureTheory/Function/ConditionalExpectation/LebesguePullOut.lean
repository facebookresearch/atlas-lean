/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalLExpectation

/-!
# Pull-out property of the conditional Lebesgue expectation

Let `m ≤ m0` be a sub-σ-algebra such that `μ.trim hm` is σ-finite. The conditional Lebesgue
expectation `μ⁻[X | m]` of a function `X : Ω → ℝ≥0∞` (`MeasureTheory.condLExp`) has the
pull-out property: an `m`-measurable factor `g : Ω → ℝ≥0∞` can be taken out,
`μ⁻[g * X | m] =ᵐ[μ] g * μ⁻[X | m]`. Both sides take values in `ℝ≥0∞`, so no integrability or
finiteness of `g` or `X` is assumed, only a.e.-measurability of `X`.

The module `Mathlib.MeasureTheory.Function.ConditionalLExpectation` lists the pull-out property
as a to-do; this file supplies it.

## Main results

* `MeasureTheory.condLExp_mul_of_measurable_left`: `μ⁻[g * X | m] =ᵐ[μ] g * μ⁻[X | m]` for an
  `m`-measurable `g : Ω → ℝ≥0∞`.
* `MeasureTheory.condLExp_indicator`: `μ⁻[s.indicator X | m] =ᵐ[μ] s.indicator (μ⁻[X | m])`
  for an `m`-measurable set `s`.

## Implementation notes

Both sides are `m`-measurable, so by `MeasureTheory.ae_eq_condLExp` it suffices to compare their
integrals over `m`-measurable sets. The comparison goes by induction on `g`
(`Measurable.ennreal_induction`): indicators of `m`-measurable sets by
`MeasureTheory.setLIntegral_condLExp`, then sums and monotone limits. The indicator form is the
case `g = s.indicator 1`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure[m0] Ω}

private theorem nsa_aux_s1a_pullout_measurable {Ω : Type*} {m m0 : MeasurableSpace Ω}
    {μ : Measure[m0] Ω} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {g X : Ω → ℝ≥0∞} (hg : Measurable[m] g) (hX : Measurable[m0] X) :
    μ⁻[g * X | m] =ᵐ[μ] g * μ⁻[X | m] := by
  have hY : Measurable[m] (μ⁻[X | m]) := measurable_condLExp m μ X
  have hYm0 : Measurable[m0] (μ⁻[X | m]) := hY.mono hm le_rfl
  have hRHS : Measurable[m] (g * μ⁻[X | m]) := hg.mul hY
  symm
  apply ae_eq_condLExp hm _ _ hRHS
  intro s hs
  simp only [Pi.mul_apply]
  refine hg.ennreal_induction ?_ ?_ ?_
  · intro c t ht
    have ht0 : MeasurableSet[m0] t := hm t ht
    have hinter : MeasurableSet[m] (t ∩ s) := ht.inter hs
    have hYeq : (fun ω => (t.indicator (fun _ => c) ω) * μ⁻[X | m] ω)
        = t.indicator (fun ω => c * μ⁻[X | m] ω) := by
      funext ω
      by_cases hω : ω ∈ t <;> simp [hω]
    have hXeq : (fun ω => (t.indicator (fun _ => c) ω) * X ω)
        = t.indicator (fun ω => c * X ω) := by
      funext ω
      by_cases hω : ω ∈ t <;> simp [hω]
    rw [hYeq, hXeq, setLIntegral_indicator ht0, setLIntegral_indicator ht0,
      lintegral_const_mul _ hYm0, lintegral_const_mul _ hX,
      setLIntegral_condLExp hm _ _ hinter]
  · intro f1 f2 _ hf1 hf2 ih1 ih2
    have hf10 : Measurable[m0] f1 := hf1.mono hm le_rfl
    have hf20 : Measurable[m0] f2 := hf2.mono hm le_rfl
    have h1Y : Measurable[m0] (fun ω => f1 ω * μ⁻[X | m] ω) := hf10.mul hYm0
    have h1X : Measurable[m0] (fun ω => f1 ω * X ω) := hf10.mul hX
    have haddY : (fun ω => (f1 ω + f2 ω) * μ⁻[X | m] ω)
        = (fun ω => f1 ω * μ⁻[X | m] ω + f2 ω * μ⁻[X | m] ω) := by
      funext ω
      rw [add_mul]
    have haddX : (fun ω => (f1 ω + f2 ω) * X ω)
        = (fun ω => f1 ω * X ω + f2 ω * X ω) := by
      funext ω
      rw [add_mul]
    simp only [Pi.add_apply]
    rw [haddY, haddX, lintegral_add_left h1Y, lintegral_add_left h1X, ih1, ih2]
  · intro f hf hmono ih
    have hf0 : ∀ n, Measurable[m0] (f n) := fun n => (hf n).mono hm le_rfl
    have hYseq : ∀ n, Measurable[m0] (fun ω => f n ω * μ⁻[X | m] ω) :=
      fun n => (hf0 n).mul hYm0
    have hXseq : ∀ n, Measurable[m0] (fun ω => f n ω * X ω) :=
      fun n => (hf0 n).mul hX
    have hYmono : Monotone (fun n ω => f n ω * μ⁻[X | m] ω) := by
      intro a b hab ω
      show f a ω * μ⁻[X | m] ω ≤ f b ω * μ⁻[X | m] ω
      have hle : f a ω ≤ f b ω := hmono hab ω
      gcongr
    have hXmono : Monotone (fun n ω => f n ω * X ω) := by
      intro a b hab ω
      show f a ω * X ω ≤ f b ω * X ω
      have hle : f a ω ≤ f b ω := hmono hab ω
      gcongr
    have hYsup : (fun ω => (⨆ n, f n ω) * μ⁻[X | m] ω)
        = (fun ω => ⨆ n, f n ω * μ⁻[X | m] ω) := by
      funext ω
      rw [ENNReal.iSup_mul]
    have hXsup : (fun ω => (⨆ n, f n ω) * X ω)
        = (fun ω => ⨆ n, f n ω * X ω) := by
      funext ω
      rw [ENNReal.iSup_mul]
    rw [hYsup, hXsup, lintegral_iSup hYseq hYmono, lintegral_iSup hXseq hXmono]
    congr 1
    funext n
    exact ih n

/-- **Pull-out property** of the conditional Lebesgue expectation: an `m`-measurable factor
`g : Ω → ℝ≥0∞` can be taken out of `μ⁻[· | m]`, that is,
`μ⁻[g * X | m] =ᵐ[μ] g * μ⁻[X | m]`. No integrability or finiteness of `g` or `X` is assumed. -/
theorem condLExp_mul_of_measurable_left (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {g X : Ω → ℝ≥0∞} (hg : Measurable[m] g) (hX : AEMeasurable[m0] X μ) :
    μ⁻[g * X | m] =ᵐ[μ] g * μ⁻[X | m] := by
  have hXm : Measurable[m0] (hX.mk X) := hX.measurable_mk
  have hXX : X =ᵐ[μ] hX.mk X := hX.ae_eq_mk
  have hgX : g * X =ᵐ[μ] g * hX.mk X := by
    filter_upwards [hXX] with ω hω
    simp only [Pi.mul_apply, hω]
  have hcond : μ⁻[g * X | m] =ᵐ[μ] μ⁻[g * hX.mk X | m] := condLExp_congr_ae hgX
  have hmain : μ⁻[g * hX.mk X | m] =ᵐ[μ] g * μ⁻[hX.mk X | m] :=
    nsa_aux_s1a_pullout_measurable hm hg hXm
  have hYeq : μ⁻[X | m] =ᵐ[μ] μ⁻[hX.mk X | m] := condLExp_congr_ae hXX
  have h3 : g * μ⁻[hX.mk X | m] =ᵐ[μ] g * μ⁻[X | m] := by
    filter_upwards [hYeq.symm] with ω hω
    simp only [Pi.mul_apply, hω]
  exact hcond.trans (hmain.trans h3)

/-- The conditional Lebesgue expectation commutes with the indicator of an `m`-measurable set:
`μ⁻[s.indicator X | m] =ᵐ[μ] s.indicator (μ⁻[X | m])`. -/
theorem condLExp_indicator (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] {s : Set Ω}
    (hs : MeasurableSet[m] s) {X : Ω → ℝ≥0∞} (hX : AEMeasurable[m0] X μ) :
    μ⁻[s.indicator X | m] =ᵐ[μ] s.indicator (μ⁻[X | m]) := by
  have hg : Measurable[m] (s.indicator 1 : Ω → ℝ≥0∞) := by measurability
  have hpull : μ⁻[s.indicator 1 * X | m] =ᵐ[μ] s.indicator 1 * μ⁻[X | m] :=
    condLExp_mul_of_measurable_left hm hg hX
  have hL : s.indicator X = s.indicator 1 * X := by
    funext ω
    by_cases hω : ω ∈ s
    · simp [Set.indicator_of_mem hω, Pi.mul_apply]
    · simp [Set.indicator_of_notMem hω, Pi.mul_apply]
  have hR : s.indicator (μ⁻[X | m]) = s.indicator 1 * μ⁻[X | m] := by
    funext ω
    by_cases hω : ω ∈ s
    · simp [Set.indicator_of_mem hω, Pi.mul_apply]
    · simp [Set.indicator_of_notMem hω, Pi.mul_apply]
  rw [hL, hR]
  exact hpull

end MeasureTheory
