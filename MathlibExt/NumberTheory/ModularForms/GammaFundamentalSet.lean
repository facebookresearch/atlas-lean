/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_FLT_Gamma0FundamentalSet_integral_gammaFundamentalSet_eq_finsum_integral_fd.lean`,
`Definitions/Def_AutomorphicForm_Gamma0FundamentalSet.lean`,
`Definitions/Def_AutomorphicForm_HyperbolicMeasure.lean`,
`Definitions/Def_AutomorphicForm_Gamma0ExactVolume.lean`
and
`P2M/Sol/S_FLT_Gamma0FundamentalSet_integral_gammaFundamentalSet_eq_finsum_integral_fd.lean`
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

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.NumberTheory.Modular
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.Index

@[expose] public section

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular Pointwise

/-- The fundamental set for a subgroup `Γ` of `SL(2, ℤ)`, obtained by
translating the standard fundamental domain `𝒟` by coset representatives
for `SL(2, ℤ) ⧸ Γ`. -/
public noncomputable def gammaFundamentalSet (Γ : Subgroup SL(2, ℤ)) : Set ℍ :=
  ⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • 𝒟

private theorem volume_smul_sl2z (γ : SL(2, ℤ)) (s : Set ℍ) :
    volume (γ • s) = volume s := by
  have h : γ • s = (Matrix.SpecialLinearGroup.mapGL ℝ γ) • s := by
    ext z
    simp only [Set.mem_smul_set_iff_inv_smul_mem, ← MulAction.compHom_smul_def]
  rw [h]
  exact MeasureTheory.measure_smul (volume : Measure ℍ) _ s

private theorem volume_eq_zero_of_image_null {s : Set ℍ}
    (h : volume ((↑) '' s : Set ℂ) = 0) : volume s = 0 := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  exact setLIntegral_measure_zero _ _ h

private theorem volume_re_eq_zero (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have hset : {z : ℂ | z.re = c} =
      Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (Set.univ : Set ℝ)) := by
    ext z
    simp [Set.mem_prod]
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet)]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod, Real.volume_singleton, zero_mul]

private theorem volume_normSq_eq_one : volume {z : ℂ | Complex.normSq z = 1} = 0 := by
  have hsub : {z : ℂ | Complex.normSq z = 1} ⊆ Metric.sphere (0 : ℂ) 1 := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [Metric.mem_sphere, dist_zero_right]
    nlinarith [Complex.normSq_eq_norm_sq z, norm_nonneg z]
  exact measure_mono_null hsub (Measure.addHaar_sphere volume 0 1)

private theorem volume_fd_diff_fdo : volume (𝒟 \ 𝒟ᵒ) = 0 := by
  apply volume_eq_zero_of_image_null
  apply measure_mono_null (t := {z : ℂ | Complex.normSq z = 1} ∪
    ({z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -(1 / 2)}))
  · rintro w ⟨z, ⟨⟨hn, hr⟩, hz⟩, rfl⟩
    simp only [ModularGroup.fdo, Set.mem_setOf_eq, not_and_or, not_lt] at hz
    rcases hz with hz | hz
    · exact Or.inl (le_antisymm hz hn)
    · right
      have habs : |z.re| = 1 / 2 := le_antisymm hr hz
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp habs with h | h
      · exact Or.inl (by simp only [Set.mem_setOf_eq, UpperHalfPlane.coe_re]; exact h)
      · exact Or.inr (by simp only [Set.mem_setOf_eq, UpperHalfPlane.coe_re]; exact h)
  · refine measure_union_null volume_normSq_eq_one (measure_union_null ?_ ?_) <;>
      exact volume_re_eq_zero _

private instance : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul γ := by
    have h : (fun z : ℍ => γ • z) =
        fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ) • z := by
      funext z
      exact MulAction.compHom_smul_def (Matrix.SpecialLinearGroup.mapGL ℝ) γ z
    rw [h]
    exact continuous_const_smul _

private theorem measurableSet_smul_fd (γ : SL(2, ℤ)) :
    MeasurableSet (γ • (𝒟 : Set ℍ)) :=
  (ModularGroup.isClosed_fd.smul γ).measurableSet

private theorem measurePreserving_smul (γ : SL(2, ℤ)) :
    MeasurePreserving (fun w : ℍ => γ • w) volume volume := by
  have hemb : MeasurableEmbedding (fun w : ℍ => γ • w) :=
    (Homeomorph.smul γ (α := ℍ)).measurableEmbedding
  exact ⟨hemb.measurable, by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Set.preimage_smul,
      volume_smul_sl2z]⟩

private theorem setIntegral_smul_fd {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (γ : SL(2, ℤ)) (f : ℍ → E) :
    ∫ u in γ • (𝒟 : Set ℍ), f u = ∫ w in (𝒟 : Set ℍ), f (γ • w) := by
  rw [← Set.image_smul]
  exact (measurePreserving_smul γ).setIntegral_image_emb
    (Homeomorph.smul γ (α := ℍ)).measurableEmbedding f _

private theorem aedisjoint_tiles {Γ : Subgroup SL(2, ℤ)}
    (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) {q q' : SL(2, ℤ) ⧸ Γ} (hqq' : q ≠ q') :
    AEDisjoint volume ((Quotient.out q)⁻¹ • (𝒟 : Set ℍ))
      ((Quotient.out q')⁻¹ • (𝒟 : Set ℍ)) := by
  set a := (Quotient.out q : SL(2, ℤ))
  set b := (Quotient.out q' : SL(2, ℤ))
  have hset : a⁻¹ • (𝒟 : Set ℍ) ∩ b⁻¹ • (𝒟 : Set ℍ) =
      a⁻¹ • ((a * b⁻¹) • (𝒟 : Set ℍ) ∩ 𝒟) := by
    rw [Set.smul_set_inter, ← mul_smul, inv_mul_cancel_left, Set.inter_comm]
  have hne : ∀ ε : SL(2, ℤ), ε ∈ Γ → ε ∈ Subgroup.center SL(2, ℤ) →
      a * b⁻¹ ≠ ε := by
    intro ε hε hc h
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change (QuotientGroup.mk a : SL(2, ℤ) ⧸ Γ) = QuotientGroup.mk b
    rw [QuotientGroup.eq]
    have hthis : a = ε * b := by rw [← h, inv_mul_cancel_right]
    have hc' : b⁻¹ * ε⁻¹ = ε⁻¹ * b⁻¹ :=
      (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) b⁻¹)
    rw [hthis, mul_inv_rev, hc', mul_assoc, inv_mul_cancel, mul_one]
    exact Γ.inv_mem hε
  have h1 : a * b⁻¹ ≠ 1 := hne 1 Γ.one_mem (Subgroup.one_mem _)
  have h2 : a * b⁻¹ ≠ -1 := hne (-1) hΓ (by
    rw [Subgroup.mem_center_iff]; intro g; simp)
  rw [AEDisjoint, hset, volume_smul_sl2z]
  refine measure_mono_null ?_ volume_fd_diff_fdo
  rintro z ⟨hzγ, hz⟩
  refine ⟨hz, fun hzo => ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hzγ
  rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hzo hzγ with h | h
  · exact h1 (by rw [← inv_inv (a * b⁻¹), h, inv_one])
  · exact h2 (by rw [← inv_inv (a * b⁻¹), h, inv_neg_one])

/-- Unfolding the integral over the fundamental set of a finite-index
subgroup `Γ` of `SL(2, ℤ)` containing `-1`: the integral over
`gammaFundamentalSet Γ` is the coset sum, over `SL(2, ℤ) ⧸ Γ`, of the
integrals over the standard fundamental domain `𝒟` of the translated
integrand. -/
public theorem integral_gammaFundamentalSet_eq_finsum_integral_fd
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℍ → E) (hf : IntegrableOn f (gammaFundamentalSet Γ)) :
    ∫ τ in gammaFundamentalSet Γ, f τ =
      ∑ᶠ q : SL(2, ℤ) ⧸ Γ, ∫ τ in ModularGroup.fd, f ((Quotient.out q)⁻¹ • τ) := by
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex
  rw [finsum_eq_sum_of_fintype]
  unfold gammaFundamentalSet at hf ⊢
  rw [integral_iUnion_ae (fun q => (measurableSet_smul_fd _).nullMeasurableSet)
    (fun q q' h => aedisjoint_tiles hΓ h) hf, tsum_fintype]
  exact Finset.sum_congr rfl fun q _ => setIntegral_smul_fd _ f
