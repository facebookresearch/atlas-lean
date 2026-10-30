/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_
setIntegral_eq_of_leftCosetRepresentatives.lean`
and
`P2M/Sol/S_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_
setIntegral_eq_of_leftCosetRepresentatives.lean`

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

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Integrals over a fundamental domain of a subgroup

If `𝓕` is a fundamental domain for `Γ₁` and `R` is a system of
representatives for the left cosets of `Γ₂` in `Γ₁`, then the translates
`((R i)⁻¹) • 𝓕` tile the union, and integrals over that union unfold
into a sum over `i` of integrals over `𝓕`.
-/

@[expose] public section

open MeasureTheory Function
open scoped Pointwise ENNReal

namespace FundamentalDomainIntegralAux

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
  [MeasurableSpace G] [MeasurableSMul G X]
  (μ : Measure X) [SMulInvariantMeasure G X μ]

omit [MeasurableSpace X] [MeasurableSpace G] [MeasurableSMul G X] in
private theorem subgroup_smul_set (Γ : Subgroup G) (γ : Γ) (s : Set X) :
    γ • s = (γ : G) • s := rfl

private theorem setLIntegral_smul_set (g : G) (s : Set X) (f : X → ℝ≥0∞) :
    ∫⁻ x in g • s, f x ∂μ = ∫⁻ x in s, f (g • x) ∂μ := by
  have he : MeasurePreserving (MeasurableEquiv.smul g : X ≃ᵐ X) μ μ :=
    measurePreserving_smul g μ
  rw [← he.setLIntegral_comp_preimage_emb (MeasurableEquiv.smul g).measurableEmbedding]
  congr 1
  change μ.restrict ((fun x => g • x) ⁻¹' (g • s)) = μ.restrict s
  rw [Set.preimage_smul, inv_smul_smul]

private theorem setIntegral_smul_set {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : G) (s : Set X) (f : X → E) :
    ∫ x in g • s, f x ∂μ = ∫ x in s, f (g • x) ∂μ := by
  have he : MeasurePreserving (MeasurableEquiv.smul g : X ≃ᵐ X) μ μ :=
    measurePreserving_smul g μ
  rw [← he.setIntegral_preimage_emb (MeasurableEquiv.smul g).measurableEmbedding]
  congr 1
  change μ.restrict ((fun x => g • x) ⁻¹' (g • s)) = μ.restrict s
  rw [Set.preimage_smul, inv_smul_smul]

end FundamentalDomainIntegralAux

namespace MeasureTheory

namespace IsFundamentalDomain

/-- If `𝓕` is a fundamental domain for `Γ₁` and `R` is a system of
representatives for the left cosets of `Γ₂` in `Γ₁`, then integrals over
the union of the translates `((R i)⁻¹) • 𝓕` unfold into sums over `i` of
integrals over `𝓕`, for both `ℝ≥0∞`-valued and Bochner integrals. -/
theorem setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
    {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (_hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    (∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, f x ∂μ = ∫⁻ x in 𝓕, ∑' i, f ((R i : G)⁻¹ • x) ∂μ) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (h : X → E),
      AEStronglyMeasurable h μ →
      ∫⁻ x in 𝓕, ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ ∂μ < ∞ →
      IntegrableOn h (⋃ i, ((R i : G)⁻¹) • 𝓕) μ ∧
      (∀ᵐ x ∂μ.restrict 𝓕, Summable fun i => ‖h ((R i : G)⁻¹ • x)‖) ∧
      ∫ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, h x ∂μ = ∫ x in 𝓕, ∑' i, h ((R i : G)⁻¹ • x) ∂μ := by
  classical
  have hnull : ∀ i, NullMeasurableSet (((R i : G)⁻¹) • 𝓕) μ := by
    intro i
    have h := h𝓕.nullMeasurableSet_smul (R i)⁻¹
    rwa [FundamentalDomainIntegralAux.subgroup_smul_set, Subgroup.coe_inv] at h
  have hdist : ∀ i j, i ≠ j → ((R i)⁻¹ : Γ₁) ≠ (R j)⁻¹ := by
    intro i j hij heq
    apply hij
    have hRi : R i = R j := inv_injective heq
    obtain ⟨k, -, hk⟩ := hR (R i)
    have hii : ((R i)⁻¹ * R i : G) ∈ Γ₂ := by
      rw [Subgroup.coe_inv, inv_mul_cancel]; exact one_mem _
    have hji : ((R j)⁻¹ * R i : G) ∈ Γ₂ := by
      rw [← hRi, Subgroup.coe_inv, inv_mul_cancel]; exact one_mem _
    exact (hk i hii).trans (hk j hji).symm
  have hdisj : Pairwise (AEDisjoint μ on fun i => ((R i : G)⁻¹) • 𝓕) := by
    intro i j hij
    have h := h𝓕.aedisjoint (hdist i j hij)
    simpa only [Function.onFun, FundamentalDomainIntegralAux.subgroup_smul_set,
      Subgroup.coe_inv] using h
  have hmp : ∀ i, MeasurePreserving (fun x : X => (R i : G)⁻¹ • x) μ μ :=
    fun i => measurePreserving_smul _ μ
  refine ⟨fun f hf => ?_, ?_⟩
  · have hfm : ∀ i, AEMeasurable (fun x => f ((R i : G)⁻¹ • x)) (μ.restrict 𝓕) := fun i =>
      ((hf.comp (measurable_const_smul ((R i : G)⁻¹)) :
        Measurable fun x => f ((R i : G)⁻¹ • x))).aemeasurable
    rw [lintegral_iUnion₀ hnull hdisj, lintegral_tsum hfm]
    exact tsum_congr fun i =>
      FundamentalDomainIntegralAux.setLIntegral_smul_set μ _ _ _
  · intro E _ _ _ h hh hfin
    have hae : ∀ i, AEStronglyMeasurable (fun x => h ((R i : G)⁻¹ • x)) (μ.restrict 𝓕) :=
      fun i => (hh.comp_measurePreserving (hmp i)).restrict
    have hnorm : ∫⁻ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, ‖h x‖ₑ ∂μ =
        ∫⁻ x in 𝓕, ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ ∂μ := by
      rw [lintegral_iUnion₀ hnull hdisj, lintegral_tsum fun i => (hae i).enorm]
      exact tsum_congr fun i =>
        FundamentalDomainIntegralAux.setLIntegral_smul_set μ _ _ _
    have hint : IntegrableOn h (⋃ i, ((R i : G)⁻¹) • 𝓕) μ :=
      ⟨hh.restrict, by rw [HasFiniteIntegral, hnorm]; exact hfin⟩
    refine ⟨hint, ?_, ?_⟩
    · have hlt : ∀ᵐ x ∂μ.restrict 𝓕, ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ < ∞ :=
        ae_lt_top' (AEMeasurable.tsum fun i => (hae i).enorm) hfin.ne
      filter_upwards [hlt] with x hx
      have hx' : ∑' i, (‖h ((R i : G)⁻¹ • x)‖₊ : ℝ≥0∞) ≠ ∞ := by
        simpa only [enorm_eq_nnnorm] using hx.ne
      have hs := ENNReal.tsum_coe_ne_top_iff_summable.mp hx'
      exact NNReal.summable_coe.mpr hs
    · rw [integral_iUnion_ae hnull hdisj hint]
      have hfin' : ∑' i, ∫⁻ x, ‖h ((R i : G)⁻¹ • x)‖ₑ ∂μ.restrict 𝓕 ≠ ∞ := by
        rw [← lintegral_tsum fun i => (hae i).enorm]
        exact hfin.ne
      rw [integral_tsum hae hfin']
      exact tsum_congr fun i =>
        FundamentalDomainIntegralAux.setIntegral_smul_set μ _ _ _

end IsFundamentalDomain

end MeasureTheory
