/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean`
and
`P2M/Sol/S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean`
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

public import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.MDifferentiableDivMonicRel

/-!
# Cusp forms times powers of `E₄` and `E₆`

This file characterizes when `F Δ ^ m / (E₄ ^ a E₆ ^ b)` is a cusp form.

## Main statement

* `CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff`
-/
namespace FrickeFunctions.EisensteinPowMul

noncomputable section

open Complex UpperHalfPlane ModularForm Filter Topology
open scoped Manifold MatrixGroups ModularForm

namespace WeightLoweringCriterion

local notation "Δ" => ModularForm.discriminant

private theorem differentiableAt_comp_ofComplex {u : ℍ →
    ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (τ : ℍ) :
    DifferentiableAt ℂ (u ∘ ofComplex) (τ : ℂ) :=
  UpperHalfPlane.mdifferentiableAt_iff.1 (hu τ)

private theorem analyticOnNhd_comp_ofComplex {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) :
    AnalyticOnNhd ℂ (u ∘ ofComplex) {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd isOpen_upperHalfPlaneSet

private theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by
  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) :=
      (differentiableAt_comp_ofComplex hv τ₀).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hne : ∀ᶠ z in 𝓝 (τ₀ : ℂ), (v ∘ ofComplex) z ≠ 0 := hvc.eventually_ne hv0'
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hne] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hEq := (analyticOnNhd_comp_ofComplex hu).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  have := hEq τ.im_pos
  simpa [Function.comp, ofComplex_apply] using this

private theorem mdifferentiableAt_of_eventuallyEq {f g : ℍ → ℂ} {τ : ℍ}
    (hfg : (f ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)] (g ∘ ofComplex))
    (hg : DifferentiableAt ℂ (g ∘ ofComplex) (τ : ℂ)) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f τ :=
  UpperHalfPlane.mdifferentiableAt_iff.2 (hfg.differentiableAt_iff.2 hg)

private theorem exists_mul_eq_of_coprime {P b c H₁ H₂ : ℍ → ℂ}
    (hb : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b) (hc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) c)
    (hH₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₁) (hH₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H₂)
    (hcop : ∀ τ : ℍ, b τ ≠ 0 ∨ c τ ≠ 0)
    (h₁ : ∀ τ : ℍ, H₁ τ * b τ = P τ) (h₂ : ∀ τ : ℍ, H₂ τ * c τ = P τ) :
    ∃ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ ∀ τ : ℍ, f τ * (b τ * c τ) = P τ := by
  classical
  let f : ℍ → ℂ := fun τ => if c τ = 0 then H₂ τ / b τ else H₁ τ / c τ
  refine ⟨f, fun τ₀ => ?_, fun τ => ?_⟩
  · by_cases hc0 : c τ₀ = 0
    · have hb0 : b τ₀ ≠ 0 := (hcop τ₀).resolve_right (by simpa using hc0)
      have hbc : ContinuousAt (b ∘ ofComplex) (τ₀ : ℂ) :=
        (differentiableAt_comp_ofComplex hb τ₀).continuousAt
      have hne : ∀ᶠ z in 𝓝 (τ₀ : ℂ), (b ∘ ofComplex) z ≠ 0 :=
        hbc.eventually_ne (by simpa [Function.comp, ofComplex_apply] using hb0)
      refine mdifferentiableAt_of_eventuallyEq (g := fun τ => H₂ τ / b τ) ?_ ?_
      · filter_upwards [hne] with z hz
        simp only [Function.comp_apply] at hz ⊢
        by_cases hcz : c (ofComplex z) = 0
        · simp [f, hcz]
        · simp only [f, hcz, ite_false]
          have e1 := h₁ (ofComplex z)
          have e2 := h₂ (ofComplex z)
          field_simp
          rw [← e2] at e1
          linear_combination e1
      · exact ((differentiableAt_comp_ofComplex hH₂ τ₀).div (differentiableAt_comp_ofComplex hb τ₀)
          (by simpa [Function.comp, ofComplex_apply] using hb0))
    · have hcc : ContinuousAt (c ∘ ofComplex) (τ₀ : ℂ) :=
        (differentiableAt_comp_ofComplex hc τ₀).continuousAt
      have hne : ∀ᶠ z in 𝓝 (τ₀ : ℂ), (c ∘ ofComplex) z ≠ 0 :=
        hcc.eventually_ne (by simpa [Function.comp, ofComplex_apply] using hc0)
      refine mdifferentiableAt_of_eventuallyEq (g := fun τ => H₁ τ / c τ) ?_ ?_
      · filter_upwards [hne] with z hz
        simp only [Function.comp_apply] at hz ⊢
        simp [f, hz]
      · exact ((differentiableAt_comp_ofComplex hH₁ τ₀).div (differentiableAt_comp_ofComplex hc τ₀)
          (by simpa [Function.comp, ofComplex_apply] using hc0))
  · by_cases hcz : c τ = 0
    · simp only [f, hcz, ite_true, mul_zero]
      rw [← h₂ τ, hcz, mul_zero]
    · simp only [f, hcz, ite_false]
      rw [← h₁ τ]
      field_simp

private theorem disc_ne_zero (τ : ℍ) : Δ τ ≠ 0 := discriminant_ne_zero τ

private theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) :=
  CuspForm.discriminant.holo'

private theorem mdifferentiable_E₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₄ : ℍ → ℂ) := E₄.holo'

private theorem mdifferentiable_E₆ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₆ : ℍ → ℂ) := E₆.holo'

private theorem E₄_ne_zero_or_E₆_ne_zero (τ : ℍ) : E₄ τ ≠ 0 ∨ E₆ τ ≠ 0 := by
  by_contra h
  push Not at h
  have hΔ := discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [h.1, h.2] at hΔ
  exact disc_ne_zero τ (by rw [hΔ]; norm_num)

private theorem exists_E₄_ne_zero : ∃ τ : ℍ, E₄ τ ≠ 0 := by
  by_contra h
  push Not at h
  have : (E₄ : ModularForm 𝒮ℒ 4) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
  exact EisensteinSeries.E_ne_zero (by norm_num) ⟨2, rfl⟩ this

private theorem exists_E₆_ne_zero : ∃ τ : ℍ, E₆ τ ≠ 0 := by
  by_contra h
  push Not at h
  have : (E₆ : ModularForm 𝒮ℒ 6) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
  exact EisensteinSeries.E_ne_zero (by norm_num) ⟨3, rfl⟩ this

private theorem mem_SL (A : SL(2, ℤ)) : (A : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨A, rfl⟩

private theorem E₄_smul (A : SL(2, ℤ)) (τ : ℍ) :
    E₄ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (4 : ℤ) * E₄ τ := by
  have := SlashInvariantForm.slash_action_eqn'' E₄ (Γ := 𝒮ℒ) (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [← ModularGroup.sl_moeb] at this
  exact_mod_cast this

private theorem E₆_smul (A : SL(2, ℤ)) (τ : ℍ) :
    E₆ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (6 : ℤ) * E₆ τ := by
  have := SlashInvariantForm.slash_action_eqn'' E₆ (Γ := 𝒮ℒ) (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [← ModularGroup.sl_moeb] at this
  exact_mod_cast this

private theorem disc_smul (A : SL(2, ℤ)) (τ : ℍ) :
    Δ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

variable (a b m : ℕ)

private def Efun : ℍ → ℂ := fun τ => E₄ τ ^ a * E₆ τ ^ b

private theorem Efun_apply (τ : ℍ) : Efun a b τ = E₄ τ ^ a * E₆ τ ^ b := rfl

private theorem mdifferentiable_Efun : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Efun a b) :=
  (mdifferentiable_E₄.pow a).mul (mdifferentiable_E₆.pow b)

private theorem exists_Efun_ne_zero : ∃ τ : ℍ, Efun a b τ ≠ 0 := by
  obtain ⟨τ₄, h₄⟩ := exists_E₄_ne_zero
  by_contra h
  push Not at h
  have hprod : ∀ τ : ℍ, E₄ τ = 0 ∨ E₆ τ = 0 := fun τ =>
    (mul_eq_zero.1 (h τ)).imp eq_zero_of_pow_eq_zero eq_zero_of_pow_eq_zero
  have hmul : ∀ τ : ℍ, E₆ τ * E₄ τ = 0 := fun τ => by
    rcases hprod τ with h0 | h0 <;> simp [h0]
  have := eq_zero_of_mul_eq_zero mdifferentiable_E₆ mdifferentiable_E₄ hmul h₄
  obtain ⟨τ₆, h₆⟩ := exists_E₆_ne_zero
  exact h₆ (by simpa using congrFun this τ₆)

private theorem Efun_smul (A : SL(2, ℤ)) (τ : ℍ) :
    Efun a b (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ ((4 * a + 6 * b : ℕ) : ℤ) * Efun a b τ := by
  simp only [Efun, E₄_smul, E₆_smul, zpow_natCast, zpow_ofNat]
  ring

private theorem disc_pow_smul (A : SL(2, ℤ)) (τ : ℍ) :
    Δ (A • τ) ^ m = denom (A : GL (Fin 2) ℝ) τ ^ ((12 * m : ℕ) : ℤ) * Δ τ ^ m := by
  rw [disc_smul, zpow_natCast, zpow_ofNat]
  ring

private theorem tendsto_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    Tendsto (⇑(ModularForm.E hk) : ℍ → ℂ) atImInfty (𝓝 1) := by
  have hanal := ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk) one_pos
    one_mem_strictPeriods_SL
  have hper :=
      SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk) one_mem_strictPeriods_SL
  have hval : cuspFunction 1 (⇑(ModularForm.E hk)) 0 = 1 := by
    have h0 := qExpansion_coeff (⇑(ModularForm.E hk)) (h := (1 : ℝ)) 0
    rw [EisensteinSeries.E_qExpansion_coeff_zero hk hk2] at h0
    simpa using h0.symm
  have := (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr
    (fun τ => eq_cuspFunction τ one_ne_zero hper)
  simpa [hval] using this

private theorem tendsto_Efun : Tendsto (Efun a b) atImInfty (𝓝 1) := by
  have h4 := (tendsto_E (by norm_num : 3 ≤ 4) ⟨2, rfl⟩).pow a
  have h6 := (tendsto_E (by norm_num : 3 ≤ 6) ⟨3, rfl⟩).pow b
  have h__af := h4.mul h6
  simp [Efun] at h__af
  exact h__af

private theorem isBoundedAtImInfty_Efun : IsBoundedAtImInfty (Efun a b) :=
  (tendsto_Efun a b).isBigO_one ℝ

section Forward

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {a b m}
variable (hk : k + 4 * a + 6 * b = 12 * m) {F : ℍ → ℂ}

include hk in
private theorem slash_mul_Efun {f : ℍ → ℂ} (hf : ∀ τ : ℍ, f τ * Efun a b τ = F τ * Δ τ ^ m)
    (A : SL(2, ℤ)) (τ : ℍ) : (f ∣[k] A) τ * Efun a b τ = F (A • τ) * Δ τ ^ m := by
  have hd : (denom (A : GL (Fin 2) ℝ) τ : ℂ) ≠ 0 := denom_ne_zero _ _
  have h1 := hf (A • τ)
  rw [Efun_smul, disc_pow_smul] at h1
  rw [ModularForm.SL_slash_apply]
  have hexp : (denom (A : GL (Fin 2) ℝ) τ : ℂ) ^ (-k) =
      denom (A : GL (Fin 2) ℝ) τ ^ ((4 * a + 6 * b : ℕ) : ℤ) *
        (denom (A : GL (Fin 2) ℝ) τ ^ ((12 * m : ℕ) : ℤ))⁻¹ := by
    rw [← zpow_neg, ← zpow_add₀ hd]
    congr 1
    push_cast
    linarith
  rw [hexp]
  have h12 : (denom (A : GL (Fin 2) ℝ) τ : ℂ) ^ ((12 * m : ℕ) : ℤ) ≠ 0 := zpow_ne_zero _ hd
  field_simp
  linear_combination h1

include hk in
private theorem forward (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ τ : ℍ, f τ * (E₄ τ ^ a * E₆ τ ^ b) = F τ * Δ τ ^ m) :
    ((∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
        (F τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ) ∧
      (∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
          (F τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ) ∧
      (∀ A : SL(2, ℤ), IsZeroAtImInfty ((F ∘ (A • ·)) * Δ ^ m)) ∧
      ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) := by
  have hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f) := f.holo'
  refine ⟨⟨fun τ => f τ ^ 3 * E₆ τ ^ (3 * b), (hfhol.pow 3).mul (mdifferentiable_E₆.pow _),
      fun τ => ?_⟩,
    ⟨fun τ => f τ ^ 2 * E₄ τ ^ (2 * a), (hfhol.pow 2).mul (mdifferentiable_E₄.pow _), fun τ => ?_⟩,
    fun A => ?_, fun γ hγ τ => ?_⟩
  · rw [← hf τ]; ring
  · rw [← hf τ]; ring
  · have hfA : IsZeroAtImInfty ((⇑f : ℍ → ℂ) ∣[k] A) := CuspFormClass.zero_at_infty_slash f A
    have hEq : ((F ∘ (A • ·)) * Δ ^ m : ℍ → ℂ) = fun τ => ((⇑f : ℍ → ℂ) ∣[k] A) τ * Efun a b τ := by
      funext τ
      simp only [Pi.mul_apply, Function.comp_apply, Pi.pow_apply]
      exact (slash_mul_Efun hk hf A τ).symm
    rw [hEq]
    exact hfA.mul_boundedAtFilter (isBoundedAtImInfty_Efun a b)
  · have h := slash_mul_Efun hk hf γ τ
    have hinv : (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f := by
      have := SlashInvariantForm.slash_action_eqn f (γ : GL (Fin 2) ℝ) (Subgroup.mem_map_of_mem _
          hγ)
      simpa [ModularForm.SL_slash] using this
    rw [hinv] at h
    rw [Efun_apply, hf τ] at h
    have hΔ : Δ τ ^ m ≠ 0 := pow_ne_zero _ (disc_ne_zero τ)
    exact (mul_left_injective₀ hΔ h).symm

end Forward

section Backward

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {a b m}
variable (hk : k + 4 * a + 6 * b = 12 * m) {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)

include hF in
private theorem exists_div_E₄ (h : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧
      ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ) :
    ∃ H : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H ∧ ∀ τ : ℍ, H τ * E₄ τ ^ a = F τ * Δ τ ^ m := by
  classical
  obtain ⟨G, hG, hrel⟩ := h
  let P : ℍ → ℂ := fun τ => F τ * Δ τ ^ m
  let B : ℍ → ℂ := fun τ => E₄ τ ^ a
  let c : ℕ → ℍ → ℂ := fun i => if i = 0 then -G else 0
  have hP : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P := hF.mul (mdifferentiable_disc.pow m)
  have hB : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) B := mdifferentiable_E₄.pow a
  have hB0 : B ≠ 0 := by
    obtain ⟨τ, hτ⟩ := exists_E₄_ne_zero
    intro hB0
    exact pow_ne_zero a hτ (by simpa [B] using congrFun hB0 τ)
  have hc : ∀ i < 3, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c i) := by
    intro i _
    by_cases hi : i = 0
    · simpa [c, hi] using hG.neg
    · have h__af := (mdifferentiable_const : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun _ : ℍ => (0 : ℂ))
      simp [c, hi] at h__af ⊢
      exact h__af
  have hmonic : P ^ 3 + ∑ i ∈ Finset.range 3, c i * B ^ (3 - i) * P ^ i = 0 := by
    funext τ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      Pi.zero_apply, c, P, B]
    simp only [ite_true, show (1 : ℕ) ≠ 0 from one_ne_zero, show (2 : ℕ) ≠ 0 from two_ne_zero,
        ite_false,
      Pi.neg_apply, Pi.zero_apply]
    rw [hrel τ]; ring
  obtain ⟨H, hH, hHB⟩ := UpperHalfPlane.exists_mdifferentiable_div_of_monicRel hP hB hB0 hc hmonic
  exact ⟨H, hH, fun τ => by simpa [P, B] using congrFun hHB τ⟩

include hF in
private theorem exists_div_E₆ (h : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧
      ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ) :
    ∃ H : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H ∧ ∀ τ : ℍ, H τ * E₆ τ ^ b = F τ * Δ τ ^ m := by
  classical
  obtain ⟨G, hG, hrel⟩ := h
  let P : ℍ → ℂ := fun τ => F τ * Δ τ ^ m
  let B : ℍ → ℂ := fun τ => E₆ τ ^ b
  let c : ℕ → ℍ → ℂ := fun i => if i = 0 then -G else 0
  have hP : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P := hF.mul (mdifferentiable_disc.pow m)
  have hB : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) B := mdifferentiable_E₆.pow b
  have hB0 : B ≠ 0 := by
    obtain ⟨τ, hτ⟩ := exists_E₆_ne_zero
    intro hB0
    exact pow_ne_zero b hτ (by simpa [B] using congrFun hB0 τ)
  have hc : ∀ i < 2, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c i) := by
    intro i _
    by_cases hi : i = 0
    · simpa [c, hi] using hG.neg
    · have h__af := (mdifferentiable_const : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun _ : ℍ => (0 : ℂ))
      simp [c, hi] at h__af ⊢
      exact h__af
  have hmonic : P ^ 2 + ∑ i ∈ Finset.range 2, c i * B ^ (2 - i) * P ^ i = 0 := by
    funext τ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Pi.add_apply, Pi.mul_apply,
        Pi.pow_apply,
      Pi.zero_apply, c, P, B]
    simp only [ite_true, show (1 : ℕ) ≠ 0 from one_ne_zero, ite_false, Pi.neg_apply, Pi.zero_apply]
    rw [hrel τ]; ring
  obtain ⟨H, hH, hHB⟩ := UpperHalfPlane.exists_mdifferentiable_div_of_monicRel hP hB hB0 hc hmonic
  exact ⟨H, hH, fun τ => by simpa [P, B] using congrFun hHB τ⟩

include hk hF in
private theorem backward
    (h₁ : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
        (F τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ)
    (h₂ : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
        (F τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ)
    (h₃ : ∀ A : SL(2, ℤ), IsZeroAtImInfty ((F ∘ (A • ·)) * Δ ^ m))
    (h₄ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) :
    ∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k,
      ∀ τ : ℍ, f τ * (E₄ τ ^ a * E₆ τ ^ b) = F τ * Δ τ ^ m := by
  obtain ⟨H₁, hH₁, hH₁E⟩ := exists_div_E₄ hF h₁
  obtain ⟨H₂, hH₂, hH₂E⟩ := exists_div_E₆ hF h₂
  have hcop : ∀ τ : ℍ, E₄ τ ^ a ≠ 0 ∨ E₆ τ ^ b ≠ 0 := fun τ =>
    (E₄_ne_zero_or_E₆_ne_zero τ).imp (pow_ne_zero a) (pow_ne_zero b)
  obtain ⟨f, hfhol, hfE⟩ :=
      exists_mul_eq_of_coprime (mdifferentiable_E₄.pow a) (mdifferentiable_E₆.pow b)
    hH₁ hH₂ hcop hH₁E hH₂E
  have hfE' : ∀ τ : ℍ, f τ * Efun a b τ = F τ * Δ τ ^ m := hfE
  have hinv : ∀ γ ∈ Γ, f ∣[k] γ = f := by
    intro γ hγ
    have hzero : ∀ τ : ℍ, ((f ∣[k] γ) τ - f τ) * Efun a b τ = 0 := by
      intro τ
      rw [sub_mul, slash_mul_Efun hk hfE' γ τ, hfE' τ, h₄ γ hγ τ, sub_self]
    obtain ⟨τ₀, hτ₀⟩ := exists_Efun_ne_zero a b
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => (f ∣[k] γ) τ - f τ) := by
      have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[k] γ) := by
        rw [ModularForm.SL_slash]; exact hfhol.slash k _
      exact h1.sub hfhol
    have := eq_zero_of_mul_eq_zero hdiff (mdifferentiable_Efun a b) hzero hτ₀
    funext τ
    exact sub_eq_zero.1 (by simpa using congrFun this τ)
  have hcusp : ∀ A : SL(2, ℤ), IsZeroAtImInfty (f ∣[k] A) := by
    intro A
    have hE1 : Tendsto (Efun a b) atImInfty (𝓝 1) := tendsto_Efun a b
    have hne : ∀ᶠ τ in atImInfty, Efun a b τ ≠ 0 := hE1.eventually_ne one_ne_zero
    have hq : Tendsto (fun τ => ((F ∘ (A • ·)) * Δ ^ m) τ / Efun a b τ) atImInfty (𝓝 0) := by
      have h__af := (h₃ A).div hE1 one_ne_zero
      simp at h__af
      exact h__af
    refine (hq.congr' ?_)
    filter_upwards [hne] with τ hτ
    rw [div_eq_iff hτ]
    simpa [Pi.mul_apply, Function.comp_apply, Pi.pow_apply] using (slash_mul_Efun hk hfE' A τ).symm
  let fC : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k :=
    { toFun := f
      slash_action_eq' := by
        rintro _ ⟨γ, hγ, rfl⟩
        have := hinv γ hγ
        rwa [ModularForm.SL_slash] at this
      holo' := hfhol
      zero_at_cusps' := fun {c} hc =>
        (OnePoint.isZeroAt_iff_forall_SL2Z
          ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)).mpr fun A _ => hcusp A }
  exact ⟨fC, fun τ => hfE τ⟩

end Backward

private theorem main (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    (∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, ∀ τ : ℍ,
        f τ * (E₄ τ ^ a * E₆ τ ^ b) = F τ * Δ τ ^ m) ↔
      ((∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
          (F τ * Δ τ ^ m) ^ 3 = E₄ τ ^ (3 * a) * G τ) ∧
        (∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
          (F τ * Δ τ ^ m) ^ 2 = E₆ τ ^ (2 * b) * G τ) ∧
        (∀ A : SL(2, ℤ), IsZeroAtImInfty ((F ∘ (A • ·)) * Δ ^ m)) ∧
        ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) :=
  ⟨fun ⟨f, hf⟩ => forward hk f hf, fun ⟨h₁, h₂, h₃, h₄⟩ => backward hk hF h₁ h₂ h₃ h₄⟩

end WeightLoweringCriterion

end

open scoped Manifold MatrixGroups ModularForm

/-- Let `Γ` be a finite-index subgroup of `SL(2, ℤ)`, `k + 4a + 6b = 12m`, and `F` holomorphic.
There is a cusp form `f` of weight `k` on `Γ` with `f E₄ ^ a E₆ ^ b = F Δ ^ m` if and only if
`(F Δ ^ m) ^ 3` is `E₄ ^ (3a)` times a holomorphic function, `(F Δ ^ m) ^ 2` is `E₆ ^ (2b)`
times a holomorphic function, `(F ∘ (A • ·)) Δ ^ m` vanishes at `i∞` for every `A : SL(2, ℤ)`,
and `F` is `Γ`-invariant. -/
public theorem _root_.CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff (Γ : Subgroup SL(2,
    ℤ)) [Γ.FiniteIndex]
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (F : UpperHalfPlane → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    (∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, ∀ τ : UpperHalfPlane,
        f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) =
          F τ * ModularForm.discriminant τ ^ m) ↔
      ((∃ G : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : UpperHalfPlane,
          (F τ * ModularForm.discriminant τ ^ m) ^ 3 = ModularForm.E₄ τ ^ (3 * a) * G τ) ∧
        (∃ G : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : UpperHalfPlane,
          (F τ * ModularForm.discriminant τ ^ m) ^ 2 = ModularForm.E₆ τ ^ (2 * b) * G τ) ∧
        (∀ A : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty
          ((F ∘ (A • ·)) * ModularForm.discriminant ^ m)) ∧
        ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) :=
  WeightLoweringCriterion.main Γ k a b m hk F hF

end EisensteinPowMul

end FrickeFunctions
