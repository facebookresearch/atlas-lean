/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

/-
Adapted from `anthropics/fermats-last-theorem` at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`:
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MeasureTheory_integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one.lean
with its corresponding `Theorems/Thm_` wrapper.
Source: https://github.com/anthropics/fermats-last-theorem
The subgroup proof is generalized to measure-preserving actions; the
extraction framework is removed. Adaptations copyright (c) Meta Platforms,
Inc. and affiliates, under the license in the root LICENSE file.
The upstream NOTICE also credits Mathlib:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in their file headers.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Banach-valued integrals through normalized action densities

An invariant Banach-valued observable integrable for one normalized density is
integrable for every such density, with the same integral. Ambient a.e. strong
measurability is derived from the first weighted measure, not assumed.

The densities may vanish. They are finite everywhere and normalized on every
orbit. No topology on the action space, Haar measure, or compactness is needed.
-/

public section

open scoped ENNReal

namespace MeasureTheory

section Descent

variable {A X : Type*} [SMul A X] [MeasurableSpace A] [MeasurableSpace X]
  (τ : Measure A) [SFinite τ] (μ : Measure X) [SFinite μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem measurePreserving_skew_smul
    (hact : Measurable fun p : A × X => p.1 • p.2)
    (hμ : ∀ a : A, MeasurePreserving (fun x : X => a • x) μ μ) :
    MeasurePreserving (fun p : A × X => (p.1, p.1 • p.2)) (τ.prod μ) (τ.prod μ) :=
  (MeasurePreserving.id τ).skew_product hact (ae_of_all _ fun a => (hμ a).map_eq)

/-- An invariant Banach-valued function a.e. strongly measurable for a
normalized weighted measure is a.e. strongly measurable for the ambient
measure. The density may vanish, so reverse absolute continuity is not assumed. -/
theorem aestronglyMeasurable_of_withDensity_of_normalized_smul
    (hact : Measurable fun p : A × X => p.1 • p.2)
    (hμ : ∀ a : A, MeasurePreserving (fun x : X => a • x) μ μ)
    {w : X → ℝ≥0∞} (hw : Measurable w)
    (h₁ : ∀ x, ∫⁻ a, w (a • x) ∂τ = 1) (hwt : ∀ x, w x ≠ ∞)
    {f : X → E} (hfinv : ∀ (a : A) (x : X), f (a • x) = f x)
    (hf : AEStronglyMeasurable f (μ.withDensity w)) : AEStronglyMeasurable f μ := by
  let f₀ := hf.mk f
  have hf₀ : StronglyMeasurable f₀ := hf.stronglyMeasurable_mk
  have hae : ∀ᵐ x ∂μ, w x ≠ 0 → f x = f₀ x := (ae_withDensity_iff hw).mp hf.ae_eq_mk
  have hp : ∀ᵐ p : A × X ∂τ.prod μ, w (p.1 • p.2) ≠ 0 →
      f (p.1 • p.2) = f₀ (p.1 • p.2) :=
    (measurePreserving_skew_smul τ μ hact hμ).quasiMeasurePreserving.snd.ae hae
  have hgood : ∀ᵐ x ∂μ, ∀ᵐ a ∂τ, w (a • x) ≠ 0 → f (a • x) = f₀ (a • x) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := μ) (ν := τ)).quasiMeasurePreserving.ae hp)
  have hswap : Measurable fun p : X × A => p.2 • p.1 := hact.comp measurable_swap
  refine ⟨fun x => ∫ a, (w (a • x)).toReal • f₀ (a • x) ∂τ, ?_, ?_⟩
  · exact (((hw.comp hswap).ennreal_toReal.stronglyMeasurable).smul
      (hf₀.comp_measurable hswap)).integral_prod_right'
  · filter_upwards [hgood] with x hx
    have heq : (fun a => (w (a • x)).toReal • f₀ (a • x)) =ᵐ[τ]
        fun a => (w (a • x)).toReal • f x := by
      filter_upwards [hx] with a ha
      by_cases h0 : w (a • x) = 0
      · simp [h0]
      · rw [← ha h0, hfinv]
    rw [integral_congr_ae heq, integral_smul_const,
      integral_toReal (μ := τ) (f := fun a => w (a • x))
        (hw.comp (hact.comp (measurable_id.prodMk measurable_const))).aemeasurable
        (ae_of_all _ fun a => lt_top_iff_ne_top.mpr (hwt (a • x))),
      h₁ x, ENNReal.toReal_one, one_smul]

end Descent

section Transport

variable {A X : Type*} [Group A] [MulAction A X]
  [MeasurableSpace A] [MeasurableInv A] [MeasurableSpace X]
  (τ : Measure A) [SFinite τ] [τ.IsInvInvariant]
  (μ : Measure X) [SFinite μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Changing a finite-valued, orbit-normalized density preserves both
integrability and the Bochner integral of an invariant Banach-valued function.
Only integrability for the first weighted measure is assumed. -/
theorem integrable_and_integral_withDensity_eq_of_normalized_smul
    (hact : Measurable fun p : A × X => p.1 • p.2)
    (hμ : ∀ a : A, MeasurePreserving (fun x : X => a • x) μ μ)
    {w₁ w₂ : X → ℝ≥0∞} (hw₁ : Measurable w₁) (hw₂ : Measurable w₂)
    (h₁ : ∀ x, ∫⁻ a, w₁ (a • x) ∂τ = 1)
    (h₂ : ∀ x, ∫⁻ a, w₂ (a • x) ∂τ = 1)
    (hwt₁ : ∀ x, w₁ x ≠ ∞) (hwt₂ : ∀ x, w₂ x ≠ ∞)
    {f : X → E} (hfinv : ∀ (a : A) (x : X), f (a • x) = f x)
    (hi : Integrable f (μ.withDensity w₁)) :
    Integrable f (μ.withDensity w₂) ∧
      ∫ x, f x ∂μ.withDensity w₂ = ∫ x, f x ∂μ.withDensity w₁ := by
  have hfm := aestronglyMeasurable_of_withDensity_of_normalized_smul τ μ hact hμ
    hw₁ h₁ hwt₁ hfinv hi.aestronglyMeasurable
  have hactx (x : X) : Measurable fun a : A => a • x :=
    hact.comp (measurable_id.prodMk measurable_const)
  have hactinv : Measurable fun p : A × X => p.1⁻¹ • p.2 :=
    hact.comp (measurable_fst.inv.prodMk measurable_snd)
  have hwlt₁ : ∀ x, w₁ x < ∞ := fun x => lt_top_iff_ne_top.mpr (hwt₁ x)
  have hwlt₂ : ∀ x, w₂ x < ∞ := fun x => lt_top_iff_ne_top.mpr (hwt₂ x)
  let K : A × X → E := fun p => (w₁ p.2).toReal • ((w₂ (p.1 • p.2)).toReal • f p.2)
  let L : A × X → E := fun p => (w₁ (p.1⁻¹ • p.2)).toReal • ((w₂ p.2).toReal • f p.2)
  have hΨ : MeasurePreserving (fun p : A × X => (p.1, p.1⁻¹ • p.2))
      (τ.prod μ) (τ.prod μ) :=
    (MeasurePreserving.id τ).skew_product hactinv (ae_of_all _ fun a => (hμ a⁻¹).map_eq)
  have hKL : K ∘ (fun p : A × X => (p.1, p.1⁻¹ • p.2)) = L := by
    funext p
    simp only [K, L, Function.comp_apply, smul_inv_smul, hfinv]
  have hKm : AEStronglyMeasurable K (τ.prod μ) :=
    (hw₁.comp measurable_snd).ennreal_toReal.aestronglyMeasurable.smul
      ((hw₂.comp hact).ennreal_toReal.aestronglyMeasurable.smul hfm.comp_snd)
  have hwf : Integrable (fun x => (w₁ x).toReal • f x) μ :=
    (integrable_withDensity_iff_integrable_smul' hw₁ (ae_of_all _ hwlt₁)).mp hi
  have hKi : Integrable K (τ.prod μ) := by
    refine (integrable_prod_iff' hKm).mpr ⟨ae_of_all _ fun x => ?_, ?_⟩
    · have hwi : Integrable (fun a => (w₂ (a • x)).toReal) τ :=
        integrable_toReal_of_lintegral_ne_top (hw₂.comp (hactx x)).aemeasurable
          (by rw [h₂ x]; exact ENNReal.one_ne_top)
      exact (hwi.smul_const (f x)).smul ((w₁ x).toReal)
    · have hnorm : (fun x => ∫ a, ‖K (a, x)‖ ∂τ) = fun x => ‖(w₁ x).toReal • f x‖ := by
        funext x
        simp only [K, norm_smul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
        rw [integral_const_mul, integral_mul_const,
          integral_toReal (μ := τ) (f := fun a => w₂ (a • x)) (hw₂.comp (hactx x)).aemeasurable
            (ae_of_all _ fun a => hwlt₂ (a • x)),
          h₂ x, ENNReal.toReal_one, one_mul]
      rw [hnorm]
      exact hwf.norm
  have hLi : Integrable L (τ.prod μ) := by
    rw [← hKL]
    exact hΨ.integrable_comp_of_integrable hKi
  have hKint : ∫ p, K p ∂τ.prod μ = ∫ x, (w₁ x).toReal • f x ∂μ := by
    rw [integral_prod_symm K hKi]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [K]
    rw [integral_smul, integral_smul_const,
      integral_toReal (μ := τ) (f := fun a => w₂ (a • x)) (hw₂.comp (hactx x)).aemeasurable
        (ae_of_all _ fun a => hwlt₂ (a • x)),
      h₂ x, ENNReal.toReal_one, one_smul]
  have hLinner (x : X) : ∫ a, L (a, x) ∂τ = (w₂ x).toReal • f x := by
    simp only [L]
    rw [integral_smul_const,
      integral_toReal (μ := τ) (f := fun a => w₁ (a⁻¹ • x))
        (hw₁.comp ((hactx x).comp measurable_inv)).aemeasurable
        (ae_of_all _ fun a => hwlt₁ (a⁻¹ • x)),
      lintegral_inv_eq_self (μ := τ) (fun a => w₁ (a • x)),
      h₁ x, ENNReal.toReal_one, one_smul]
  have hLint : ∫ p, L p ∂τ.prod μ = ∫ x, (w₂ x).toReal • f x ∂μ := by
    rw [integral_prod_symm L hLi]
    exact integral_congr_ae (ae_of_all _ hLinner)
  have hKLint : ∫ p, K p ∂τ.prod μ = ∫ p, L p ∂τ.prod μ := by
    have h := integral_map (μ := τ.prod μ) hΨ.measurable.aemeasurable
      (f := K) (by rw [hΨ.map_eq]; exact hKm)
    rw [hΨ.map_eq] at h
    rw [h, ← hKL]
    rfl
  refine ⟨?_, ?_⟩
  · rw [integrable_withDensity_iff_integrable_smul' hw₂ (ae_of_all _ hwlt₂)]
    exact hLi.integral_prod_right.congr (ae_of_all _ hLinner)
  · rw [integral_withDensity_eq_integral_toReal_smul hw₂ (ae_of_all _ hwlt₂),
      integral_withDensity_eq_integral_toReal_smul hw₁ (ae_of_all _ hwlt₁),
      ← hLint, ← hKLint, hKint]

end Transport

end MeasureTheory
