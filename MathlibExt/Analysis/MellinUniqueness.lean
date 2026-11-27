/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_LanglandsTunnell_HonestLDatum.lean`,
`Theorems/Thm_LanglandsTunnell_Converse_MellinUniqueness_eq_of_forall_continuous_char_laplace_
eq.lean`,
`Theorems/Thm_LanglandsTunnell_Converse_MellinUniqueness_eq_of_forall_continuous_char_exists_
laplace_eq.lean`,
`P2M/Sol/S_LanglandsTunnell_Converse_MellinUniqueness_eq_of_forall_continuous_char_laplace_eq.lean`
and
`P2M/Sol/S_LanglandsTunnell_Converse_MellinUniqueness_eq_of_forall_continuous_char_exists_laplace_
eq.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import MathlibExt.Analysis.Complex.BoundedOnStrips
public import MathlibExt.Analysis.LaplaceUniqueness
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Prod

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

@[expose] public section

noncomputable section

open MeasureTheory
open LanglandsTunnell Complex Filter Set
open scoped Topology ComplexConjugate

namespace LanglandsTunnell.Converse.MellinUniqueness

private theorem lvqInt {C : Type*} [TopologicalSpace C] [CompactSpace C] [MeasurableSpace C]
    [OpensMeasurableSpace C] {μ : Measure C} [IsFiniteMeasureOnCompacts μ] {f : C → ℂ}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

private noncomputable def lvqPair {C : Type*} [TopologicalSpace C] [CompactSpace C]
  [MeasurableSpace C]
    [OpensMeasurableSpace C] (μ : Measure C) [IsFiniteMeasureOnCompacts μ] (F : C(C, ℂ)) :
    C(C, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ x, F x * g x ∂μ
      map_add' := fun g g' => by
        simp only [ContinuousMap.add_apply, mul_add]
        exact integral_add (lvqInt (F.continuous.mul g.continuous))
          (lvqInt (F.continuous.mul g'.continuous))
      map_smul' := fun a g => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        calc ∫ x, F x * (a * g x) ∂μ = ∫ x, a * (F x * g x) ∂μ := by
              congr 1
              funext x
              ring
          _ = a * ∫ x, F x * g x ∂μ := integral_const_mul a _ }
    (∫ x, ‖F x‖ ∂μ) (fun g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ x, F x * g x ∂μ‖ ≤ ∫ x, ‖F x‖ * ‖g‖ ∂μ :=
            norm_integral_le_of_norm_le ((lvqInt F.continuous).norm.mul_const _)
              (ae_of_all _ fun x => by
                rw [norm_mul]
                gcongr
                exact g.norm_coe_le_norm x)
        _ = (∫ x, ‖F x‖ ∂μ) * ‖g‖ := integral_mul_const _ _)

private theorem lvqPair_apply {C : Type*} [TopologicalSpace C] [CompactSpace C] [MeasurableSpace C]
    [OpensMeasurableSpace C] (μ : Measure C) [IsFiniteMeasureOnCompacts μ] (F g : C(C, ℂ)) :
    lvqPair μ F g = ∫ x, F x * g x ∂μ :=
  rfl

open scoped Pointwise in
private theorem lvqZero {C : Type*} [Group C] [TopologicalSpace C] [CompactSpace C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure]
    (hsep : ∀ x : C, x ≠ 1 → ∃ χ : C →* ℂˣ, Continuous χ ∧ χ x ≠ 1)
    (F : C → ℂ) (hF : Continuous F)
    (h : ∀ χ : C →* ℂˣ, Continuous χ → ∫ x, F x * (χ x : ℂ) ∂μ = 0) : F = 0 := by
  set Fc : C(C, ℂ) := ⟨F, hF⟩ with hFc
  set ℓ : C(C, ℂ) →L[ℂ] ℂ := lvqPair μ Fc with hℓ
  set Kr : Submodule ℂ C(C, ℂ) := LinearMap.ker (ℓ : C(C, ℂ) →ₗ[ℂ] ℂ) with hKr
  set S : Set C(C, ℂ) := {g | ∃ χ : C →* ℂˣ, Continuous χ ∧ ⇑g = fun x => (χ x : ℂ)} with hS
  have hS1 : (1 : C(C, ℂ)) ∈ S := ⟨1, continuous_const, by funext x; simp⟩
  have hSmul : ∀ g ∈ S, ∀ g' ∈ S, g * g' ∈ S := by
    rintro g ⟨χ, hχ, hg⟩ g' ⟨χ', hχ', hg'⟩
    refine ⟨χ * χ', hχ.mul hχ', ?_⟩
    funext x
    simp [hg, hg']
  have hSstar : ∀ g ∈ S, star g ∈ S := by
    rintro g ⟨χ, hχ, hg⟩
    refine ⟨(Units.map (starRingEnd ℂ : ℂ →* ℂ)).comp χ,
      (Continuous.units_map _ Complex.continuous_conj).comp hχ, ?_⟩
    funext x
    simp [hg]
  have hSker : S ⊆ (Kr : Set C(C, ℂ)) := by
    rintro g ⟨χ, hχ, hg⟩
    have h0 : ℓ g = 0 := by
      rw [hℓ, lvqPair_apply]
      have e : ∀ x, Fc x * g x = F x * (χ x : ℂ) := fun x => by rw [hg]; rfl
      simp_rw [e]
      exact h χ hχ
    simpa [hKr] using h0

  set A : StarSubalgebra ℂ C(C, ℂ) := StarAlgebra.adjoin ℂ S with hA
  let M : Submonoid C(C, ℂ) :=
    { carrier := S
      one_mem' := hS1
      mul_mem' := fun {a b} ha hb => hSmul a ha b hb }
  have hstarS : star S ⊆ S := fun g hg => by
    have := hSstar _ (Set.mem_star.1 hg)
    rwa [star_star] at this
  have hcl : (Submonoid.closure (S ∪ star S) : Set C(C, ℂ)) ⊆ S :=
    (Submonoid.closure_le (S := M)).2 (Set.union_subset subset_rfl hstarS)
  have hAker : (A : Set C(C, ℂ)) ⊆ (Kr : Set C(C, ℂ)) := by
    intro g hg
    have hg' : g ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (S ∪ star S)) := by
      rw [Subalgebra.mem_toSubmodule, ← StarAlgebra.adjoin_toSubalgebra]
      exact hg
    rw [Algebra.adjoin_eq_span] at hg'
    exact Submodule.span_le.2 (hcl.trans hSker) hg'

  have hsepA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨χ, hχ, hne⟩ := hsep (x * y⁻¹) (mul_inv_eq_one.not.2 hxy)
    let g : C(C, ℂ) := ⟨fun z => (χ z : ℂ), Units.continuous_val.comp hχ⟩
    have hgA : g ∈ A := StarAlgebra.subset_adjoin ℂ S ⟨χ, hχ, rfl⟩
    refine ⟨g, ⟨g, hgA, rfl⟩, fun hxy' => hne ?_⟩
    have hval : (χ x : ℂ) = χ y := hxy'
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact Units.val_injective hval
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsepA
  have hall : ∀ g : C(C, ℂ), ℓ g = 0 := fun g => by
    have hg : g ∈ (A.topologicalClosure : Set C(C, ℂ)) := by
      rw [htop]
      trivial
    rw [StarSubalgebra.topologicalClosure_coe] at hg
    have hgK := closure_minimal hAker ℓ.isClosed_ker hg
    simpa [hKr] using hgK

  have h0 : ∫ x, (‖F x‖ ^ 2 : ℝ) ∂μ = 0 := by
    have h1 := hall (star Fc)
    rw [hℓ, lvqPair_apply] at h1
    have h2 : ∀ x, Fc x * (star Fc) x = ((‖F x‖ ^ 2 : ℝ) : ℂ) := fun x => by
      rw [ContinuousMap.star_apply]
      push_cast
      exact Complex.mul_conj' (F x)
    simp_rw [h2] at h1
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h1
    exact h1
  have hint : Integrable (fun x => ‖F x‖ ^ 2) μ :=
    (continuous_norm.comp hF).pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖F x‖) hint).1 h0
  have heq : (fun x => ‖F x‖ ^ 2) = 0 :=
    (Continuous.ae_eq_iff_eq μ (by fun_prop) continuous_const).1 hae
  funext x
  have := congr_fun heq x
  simpa using this

private theorem lvqCont {C : Type*} [TopologicalSpace C] [CompactSpace C] [MeasurableSpace C]
    [OpensMeasurableSpace C] (μ : Measure C) [IsFiniteMeasureOnCompacts μ]
    (k : C × ℝ → ℂ) (hk : Continuous k) : Continuous fun t : ℝ => ∫ x, k (x, t) ∂μ := by
  have := continuous_parametric_integral_of_continuous (μ := μ) (f := fun (t : ℝ) (x : C) => k (x,
    t))
    (by fun_prop) isCompact_univ
  simpa only [Measure.restrict_univ] using this

private theorem lvqData {C : Type*} [MeasurableSpace C] (μ : Measure C) [SFinite μ]
    (k : C × ℝ → ℂ) (s L : ℂ)
    (H : Integrable (fun p : C × ℝ => k p * cexp (s * (p.2 : ℂ))) (μ.prod volume) ∧
      ∫ p : C × ℝ, k p * cexp (s * (p.2 : ℂ)) ∂(μ.prod volume) = L) :
    Integrable (fun t : ℝ => (∫ x, k (x, t) ∂μ) * cexp (s * (t : ℂ))) ∧
      ∫ t : ℝ, (∫ x, k (x, t) ∂μ) * cexp (s * (t : ℂ)) = L := by
  have e : ∀ t : ℝ, ∫ x, k (x, t) * cexp (s * (t : ℂ)) ∂μ = (∫ x, k (x, t) ∂μ) * cexp (s * (t : ℂ))
    :=
    fun t => integral_mul_const _ _
  refine ⟨?_, ?_⟩
  · have := H.1.integral_prod_right
    simpa only [e] using this
  · rw [← H.2, integral_prod_symm _ H.1]
    simp only [e]

/-- Mellin uniqueness over a compact group: two continuous functions
with the same character-twisted Laplace transform are equal. -/
theorem eq_of_forall_continuous_char_laplace_eq
    (C : Type*) [Group C] [TopologicalSpace C] [CompactSpace C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure]
    (hsep : ∀ x : C, x ≠ 1 → ∃ χ : C →* ℂˣ, Continuous χ ∧ χ x ≠ 1)
    (f₁ f₂ : C × ℝ → ℂ) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (c : ℝ)
    (Λ : (C →* ℂˣ) → ℂ → ℂ)
    (hΛ : ∀ χ : C →* ℂˣ, Continuous χ → Differentiable ℂ (Λ χ))
    (hb : ∀ χ : C →* ℂˣ, Continuous χ → Complex.BoundedOnStrips (Λ χ))
    (h₁ : ∀ χ : C →* ℂˣ, Continuous χ → ∀ s : ℂ, c < s.re →
      Integrable (fun p : C × ℝ => f₁ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ))) (μ.prod
        volume) ∧
        ∫ p : C × ℝ, f₁ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ
          s)
    (h₂ : ∀ χ : C →* ℂˣ, Continuous χ → ∀ s : ℂ, s.re < -c →
      Integrable (fun p : C × ℝ => f₂ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ))) (μ.prod
        volume) ∧
        ∫ p : C × ℝ, f₂ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ
          s) :
    f₁ = f₂ := by
  have main : ∀ χ : C →* ℂˣ, Continuous χ →
      (fun t : ℝ => ∫ x, f₁ (x, t) * (χ x : ℂ) ∂μ) = fun t : ℝ => ∫ x, f₂ (x, t) * (χ x : ℂ) ∂μ :=
        by
    intro χ hχ
    have hχv : Continuous fun p : C × ℝ => ((χ p.1 : ℂˣ) : ℂ) :=
      Units.continuous_val.comp (hχ.comp continuous_fst)
    have hk₁ : Continuous fun p : C × ℝ => f₁ p * ((χ p.1 : ℂˣ) : ℂ) := hf₁.mul hχv
    have hk₂ : Continuous fun p : C × ℝ => f₂ p * ((χ p.1 : ℂˣ) : ℂ) := hf₂.mul hχv
    exact LanglandsTunnell.Converse.MellinUniqueness.eq_of_laplace_eq_of_boundedOnStrips _ _
      (lvqCont μ _ hk₁) (lvqCont μ _ hk₂) c (Λ χ) (hΛ χ hχ) (hb χ hχ)
      (fun s hs => lvqData μ _ s _ (h₁ χ hχ s hs)) (fun s hs => lvqData μ _ s _ (h₂ χ hχ s hs))

  have key : ∀ t : ℝ, (fun x => f₁ (x, t) - f₂ (x, t)) = 0 := by
    intro t
    have hc₁ : Continuous fun x => f₁ (x, t) := hf₁.comp (Continuous.prodMk_left t)
    have hc₂ : Continuous fun x => f₂ (x, t) := hf₂.comp (Continuous.prodMk_left t)
    refine lvqZero μ hsep _ (hc₁.sub hc₂) fun χ hχ => ?_
    have hχc : Continuous fun x => ((χ x : ℂˣ) : ℂ) := Units.continuous_val.comp hχ
    have e := congr_fun (main χ hχ) t
    have i₁ : Integrable (fun x => f₁ (x, t) * ((χ x : ℂˣ) : ℂ)) μ := lvqInt (hc₁.mul hχc)
    have i₂ : Integrable (fun x => f₂ (x, t) * ((χ x : ℂˣ) : ℂ)) μ := lvqInt (hc₂.mul hχc)
    simp_rw [sub_mul]
    rw [integral_sub i₁ i₂, e, sub_self]
  funext p
  have := congr_fun (key p.2) p.1
  simpa [sub_eq_zero] using this

/-- Mellin uniqueness over a compact group, with a strip constant
allowed to depend on the character. -/
theorem eq_of_forall_continuous_char_exists_laplace_eq
    (C : Type*) [Group C] [TopologicalSpace C] [CompactSpace C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure]
    (hsep : ∀ x : C, x ≠ 1 → ∃ χ : C →* ℂˣ, Continuous χ ∧ χ x ≠ 1)
    (f₁ f₂ : C × ℝ → ℂ) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (Λ : (C →* ℂˣ) → ℂ → ℂ)
    (hΛ : ∀ χ : C →* ℂˣ, Continuous χ → Differentiable ℂ (Λ χ))
    (hb : ∀ χ : C →* ℂˣ, Continuous χ → Complex.BoundedOnStrips (Λ χ))
    (h : ∀ χ : C →* ℂˣ, Continuous χ → ∃ c : ℝ,
      (∀ s : ℂ, c < s.re →
        Integrable (fun p : C × ℝ => f₁ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ)))
          (μ.prod volume) ∧
          ∫ p : C × ℝ, f₁ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ
            χ s) ∧
      (∀ s : ℂ, s.re < -c →
        Integrable (fun p : C × ℝ => f₂ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ)))
          (μ.prod volume) ∧
          ∫ p : C × ℝ, f₂ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ
            χ s)) :
    f₁ = f₂ := by
  have main : ∀ χ : C →* ℂˣ, Continuous χ →
      (fun t : ℝ => ∫ x, f₁ (x, t) * (χ x : ℂ) ∂μ) = fun t : ℝ => ∫ x, f₂ (x, t) * (χ x : ℂ) ∂μ :=
        by
    intro χ hχ
    obtain ⟨c, h₁χ, h₂χ⟩ := h χ hχ
    have hχv : Continuous fun p : C × ℝ => ((χ p.1 : ℂˣ) : ℂ) :=
      Units.continuous_val.comp (hχ.comp continuous_fst)
    have hk₁ : Continuous fun p : C × ℝ => f₁ p * ((χ p.1 : ℂˣ) : ℂ) := hf₁.mul hχv
    have hk₂ : Continuous fun p : C × ℝ => f₂ p * ((χ p.1 : ℂˣ) : ℂ) := hf₂.mul hχv
    exact LanglandsTunnell.Converse.MellinUniqueness.eq_of_laplace_eq_of_boundedOnStrips _ _
      (lvqCont μ _ hk₁) (lvqCont μ _ hk₂) c (Λ χ) (hΛ χ hχ) (hb χ hχ)
      (fun s hs => lvqData μ _ s _ (h₁χ s hs)) (fun s hs => lvqData μ _ s _ (h₂χ s hs))

  have key : ∀ t : ℝ, (fun x => f₁ (x, t) - f₂ (x, t)) = 0 := by
    intro t
    have hc₁ : Continuous fun x => f₁ (x, t) := hf₁.comp (Continuous.prodMk_left t)
    have hc₂ : Continuous fun x => f₂ (x, t) := hf₂.comp (Continuous.prodMk_left t)
    refine lvqZero μ hsep _ (hc₁.sub hc₂) fun χ hχ => ?_
    have hχc : Continuous fun x => ((χ x : ℂˣ) : ℂ) := Units.continuous_val.comp hχ
    have e := congr_fun (main χ hχ) t
    have i₁ : Integrable (fun x => f₁ (x, t) * ((χ x : ℂˣ) : ℂ)) μ := lvqInt (hc₁.mul hχc)
    have i₂ : Integrable (fun x => f₂ (x, t) * ((χ x : ℂˣ) : ℂ)) μ := lvqInt (hc₂.mul hχc)
    simp_rw [sub_mul]
    rw [integral_sub i₁ i₂, e, sub_self]
  funext p
  have := congr_fun (key p.2) p.1
  simpa [sub_eq_zero] using this

end LanglandsTunnell.Converse.MellinUniqueness
