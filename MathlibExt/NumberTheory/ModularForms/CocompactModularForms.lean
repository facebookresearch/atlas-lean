/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_modularForm_eq_const_and_eq_zero_of_isCompact.lean`
and
`P2M/Sol/S_ModularCurve_modularForm_eq_const_and_eq_zero_of_isCompact.lean`
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

public import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Modular forms for a cocompact group

For a discrete determinant-one subgroup of `GL (Fin 2) ℝ` whose action
on the upper half-plane is cocompact, every weight-zero modular form is
constant and every modular form of negative weight vanishes. The proof
maximises the invariant gauge `‖f τ‖² (im τ)^k` on a compact
fundamental set and applies the maximum principle.
-/

@[expose] public section

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

namespace ModularCurveCocompactAux

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ}

private noncomputable def mgauge (f : ModularForm Γ k) (τ : ℍ) : ℝ := ‖f τ‖ ^ 2 * (τ.im) ^ k

private theorem mgauge_smul (f : ModularForm Γ k) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γ) (τ : ℍ) :
    mgauge f (γ • τ) = mgauge f τ := by
  unfold mgauge
  rw [SlashInvariantForm.slash_action_eqn'' f hγ τ, UpperHalfPlane.im_smul_eq_div_normSq,
    Complex.normSq_eq_norm_sq, norm_mul, norm_zpow]
  have hdet : |γ.det.val| = 1 := by rw [Subgroup.HasDetOne.det_eq hγ]; simp
  rw [hdet, one_mul]
  have hd : ‖denom γ τ‖ ≠ 0 := norm_ne_zero_iff.mpr (denom_ne_zero γ τ)
  have hX : ‖denom γ τ‖ ^ k ≠ 0 := zpow_ne_zero k hd
  rw [div_zpow, show (‖denom γ τ‖ ^ 2) ^ k = (‖denom γ τ‖ ^ k) ^ 2 by
    rw [← zpow_natCast (‖denom γ τ‖ ^ k) 2, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]]
  field_simp

private theorem continuous_mgauge (f : ModularForm Γ k) : Continuous (mgauge f) := by
  unfold mgauge
  refine ((continuous_norm.comp f.holo'.continuous).pow 2).mul ?_
  exact Continuous.zpow₀ UpperHalfPlane.continuous_im k fun τ => Or.inl τ.im_pos.ne'

private theorem exists_forall_mgauge_le
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K)
    (f : ModularForm Γ k) : ∃ τ₀ : ℍ, ∀ τ : ℍ, mgauge f τ ≤ mgauge f τ₀ := by
  obtain ⟨K, hK, hcov⟩ := hcpt
  have hne : K.Nonempty := by
    obtain ⟨γ, -, h⟩ := hcov UpperHalfPlane.I
    exact ⟨_, h⟩
  obtain ⟨τ₀, -, hmax⟩ := hK.exists_isMaxOn hne (continuous_mgauge f).continuousOn
  refine ⟨τ₀, fun τ => ?_⟩
  obtain ⟨γ, hγ, hγτ⟩ := hcov τ
  rw [← mgauge_smul f hγ τ]
  exact hmax hγτ

private def U : Set ℂ := {z : ℂ | 0 < z.im}

private theorem isOpen_U : IsOpen U := isOpen_lt continuous_const Complex.continuous_im

private theorem convex_U : Convex ℝ U := by
  intro x hx y hy a b ha hb hab
  show 0 < (a • x + b • y).im
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab; subst hab; (simp at hy ⊢; exact hy)
  · have : 0 ≤ b * y.im := mul_nonneg hb hy.le
    nlinarith [mul_pos ha' hx]

omit [Γ.HasDetOne] in
private theorem differentiableOn_comp_ofComplex (f : ModularForm Γ k) :
    DifferentiableOn ℂ (fun z : ℂ => f (ofComplex z)) U := by
  intro z hz
  have h := (UpperHalfPlane.mdifferentiableAt_iff (f := f) (τ := ⟨z, hz⟩)).mp (f.holo' ⟨z, hz⟩)
  exact h.differentiableWithinAt

private theorem solution_aux
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [hdisc : DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K) :
    (∀ f : ModularForm Γ 0, ∃ c : ℂ, (f : ℍ → ℂ) = fun _ => c) ∧
    (∀ k : ℤ, k < 0 → ∀ f : ModularForm Γ k, (f : ℍ → ℂ) = 0) := by
  refine ⟨fun f => ?_, fun k hk f => ?_⟩
  ·
    obtain ⟨τ₀, hτ₀⟩ := exists_forall_mgauge_le hcpt f
    have hmax : IsMaxOn (norm ∘ fun z : ℂ => f (ofComplex z)) U (τ₀ : ℂ) := by
      intro z hz
      have h := hτ₀ ⟨z, hz⟩
      simp only [mgauge, zpow_zero, mul_one] at h
      have h' : ‖f ⟨z, hz⟩‖ ≤ ‖f τ₀‖ :=
        (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
      show ‖f (ofComplex z)‖ ≤ ‖f (ofComplex (τ₀ : ℂ))‖
      rw [ofComplex_apply_of_im_pos hz, ofComplex_apply]
      exact h'
    have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm convex_U.isPreconnected isOpen_U
      (differentiableOn_comp_ofComplex f) τ₀.im_pos hmax
    refine ⟨f τ₀, funext fun τ => ?_⟩
    have := heq τ.im_pos
    simp only [Function.const_apply, ofComplex_apply] at this
    exact this
  ·
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (k : ℤ) = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
    have hn1 : 1 ≤ n := by omega
    obtain ⟨τ₀, hτ₀⟩ := exists_forall_mgauge_le hcpt f
    set M : ℝ := mgauge f τ₀ with hM

    have hbd : ∀ τ : ℍ, ‖f τ‖ ^ 2 ≤ M * τ.im ^ n := by
      intro τ
      have h : mgauge f τ ≤ mgauge f τ₀ := hτ₀ τ
      unfold mgauge at h
      have hzk : (τ.im : ℝ) ^ k = (τ.im ^ n)⁻¹ := by rw [hn, zpow_neg, zpow_natCast]
      rw [hzk] at h
      change ‖f τ‖ ^ 2 * (τ.im ^ n)⁻¹ ≤ M at h
      have hy : 0 < τ.im ^ n := pow_pos τ.im_pos n
      rwa [mul_inv_le_iff₀ hy] at h

    suffices hM0 : M ≤ 0 by
      funext τ
      have h := hbd τ
      have : ‖f τ‖ ^ 2 ≤ 0 := h.trans (mul_nonpos_of_nonpos_of_nonneg hM0 (pow_pos τ.im_pos n).le)
      have : ‖f τ‖ = 0 := by nlinarith [norm_nonneg (f τ)]
      simpa using this
    by_contra hMpos
    push Not at hMpos

    set x₀ : ℝ := (τ₀ : ℂ).re with hx₀
    set y₀ : ℝ := τ₀.im with hy₀
    have hy₀pos : 0 < y₀ := τ₀.im_pos
    have hfτ₀ : ‖f τ₀‖ ^ 2 = M * y₀ ^ n := by
      have : M = ‖f τ₀‖ ^ 2 * τ₀.im ^ k := rfl
      have hzk : (τ₀.im : ℝ) ^ k = (y₀ ^ n)⁻¹ := by rw [hn, zpow_neg, zpow_natCast]
      rw [this, hzk]
      field_simp

    set w : ℂ := (starRingEnd ℂ) (τ₀ : ℂ) with hw
    have hw_im : w.im = -y₀ := by rw [hw]; simp [hy₀]
    have hw_re : w.re = x₀ := by rw [hw]; simp [hx₀]
    have hzw : ∀ z ∈ U, z - w ≠ 0 := by
      intro z hz h
      have : z.im = w.im := by rw [sub_eq_zero.mp h]
      rw [hw_im] at this
      exact absurd this (by have := hz.out; linarith)
    let G : ℂ → ℂ := fun z => f (ofComplex z) / (z - w) ^ n
    have hGd : DifferentiableOn ℂ G U := fun z hz =>
      (differentiableOn_comp_ofComplex f z hz).div
        (((differentiableAt_id.sub_const w).pow n).differentiableWithinAt)
          (pow_ne_zero n (hzw z hz))

    have hkey : ∀ z ∈ U, 4 * z.im * y₀ ≤ ‖z - w‖ ^ 2 := by
      intro z hz
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hw_im]
      nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - y₀)]

    set c2 : ℝ := M / (4 * y₀) ^ n with hc2
    have hG_le : ∀ z ∈ U, ‖G z‖ ^ 2 ≤ c2 := by
      intro z hz
      have hzw' : 0 < ‖z - w‖ := norm_pos_iff.mpr (hzw z hz)
      show ‖f (ofComplex z) / (z - w) ^ n‖ ^ 2 ≤ c2
      rw [norm_div, norm_pow, div_pow, ofComplex_apply_of_im_pos hz]
      have h1 := hbd ⟨z, hz⟩
      have h2 : (⟨z, hz⟩ : ℍ).im ^ n ≤ (‖z - w‖ ^ 2 / (4 * y₀)) ^ n := by
        apply pow_le_pow_left₀ (⟨z, hz⟩ : ℍ).im_pos.le
        rw [le_div_iff₀ (by positivity)]
        have := hkey z hz
        change z.im * (4 * y₀) ≤ _
        linarith
      rw [div_le_iff₀ (by positivity), hc2]
      calc ‖f ⟨z, hz⟩‖ ^ 2 ≤ M * (⟨z, hz⟩ : ℍ).im ^ n := h1
        _ ≤ M * (‖z - w‖ ^ 2 / (4 * y₀)) ^ n := mul_le_mul_of_nonneg_left h2 hMpos.le
        _ = M / (4 * y₀) ^ n * (‖z - w‖ ^ n) ^ 2 := by rw [div_pow, ← pow_mul, ← pow_mul]; ring

    have hz₀U : (τ₀ : ℂ) ∈ U := τ₀.im_pos
    have hG_eq : ‖G (τ₀ : ℂ)‖ ^ 2 = c2 := by
      show ‖f (ofComplex (τ₀ : ℂ)) / ((τ₀ : ℂ) - w) ^ n‖ ^ 2 = c2
      rw [norm_div, norm_pow, div_pow, ofComplex_apply, hfτ₀]
      have hnorm : ‖(τ₀ : ℂ) - w‖ = 2 * y₀ := by
        have : (τ₀ : ℂ) - w = Complex.I * (2 * y₀) := by
          apply Complex.ext <;> simp [hw_re, hw_im, hx₀, hy₀] <;> ring
        rw [this, norm_mul, Complex.norm_I, one_mul]
        simp [abs_of_pos hy₀pos]
      rw [hnorm, hc2, ← pow_mul, mul_comm n 2, pow_mul,
        show (2 * y₀) ^ 2 = (4 * y₀) * y₀ by ring, mul_pow]
      field_simp

    have hmax : IsMaxOn (norm ∘ G) U (τ₀ : ℂ) := by
      intro z hz
      show ‖G z‖ ≤ ‖G (τ₀ : ℂ)‖
      have := hG_le z hz
      rw [← hG_eq] at this
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
    have heqOn := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      convex_U.isPreconnected isOpen_U hGd
      hz₀U hmax

    set z₁ : ℂ := ⟨x₀, 2 * y₀⟩ with hz₁
    have hz₁im : z₁.im = 2 * y₀ := rfl
    have hz₁U : z₁ ∈ U := by show 0 < z₁.im; rw [hz₁im]; linarith
    have h1 : ‖G z₁‖ ^ 2 = c2 := by
      have : G z₁ = G (τ₀ : ℂ) := heqOn hz₁U
      rw [this, hG_eq]
    have hnorm1 : ‖z₁ - w‖ = 3 * y₀ := by
      have : z₁ - w = Complex.I * (3 * y₀) := by
        apply Complex.ext <;> simp [hz₁, hw_re, hw_im] <;> ring
      rw [this, norm_mul, Complex.norm_I, one_mul]
      simp [abs_of_pos hy₀pos]
    have h2 : ‖G z₁‖ ^ 2 ≤ M * (2 * y₀) ^ n / ((3 * y₀) ^ n) ^ 2 := by
      show ‖f (ofComplex z₁) / (z₁ - w) ^ n‖ ^ 2 ≤ _
      rw [norm_div, norm_pow, div_pow, ofComplex_apply_of_im_pos hz₁U, hnorm1]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := hbd ⟨z₁, hz₁U⟩
      have him : (⟨z₁, hz₁U⟩ : ℍ).im = 2 * y₀ := hz₁im
      rwa [him] at this

    have h3 : M * (2 * y₀) ^ n / ((3 * y₀) ^ n) ^ 2 < c2 := by
      rw [hc2, div_lt_div_iff₀ (by positivity) (by positivity)]
      have hlt : (2 * y₀) ^ n * (4 * y₀) ^ n < ((3 * y₀) ^ n) ^ 2 := by
        rw [← mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
        exact pow_lt_pow_left₀ (by nlinarith) (by positivity) (by omega)
      calc M * (2 * y₀) ^ n * (4 * y₀) ^ n = M * ((2 * y₀) ^ n * (4 * y₀) ^ n) := by ring
        _ < M * ((3 * y₀) ^ n) ^ 2 := mul_lt_mul_of_pos_left hlt hMpos
    linarith
end ModularCurveCocompactAux


namespace ModularCurve

/-- On a cocompact discrete determinant-one group, weight-zero modular
forms are constant and negative-weight forms vanish. -/
public theorem modularForm_eq_const_and_eq_zero_of_isCompact
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K) :
    (∀ f : ModularForm Γ 0, ∃ c : ℂ, (f : ℍ → ℂ) = fun _ => c) ∧
    (∀ k : ℤ, k < 0 → ∀ f : ModularForm Γ k, (f : ℍ → ℂ) = 0) :=
  ModularCurveCocompactAux.solution_aux Γ hcpt

end ModularCurve
