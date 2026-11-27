/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Modular

/-!
# The half-open fundamental domain of the modular group

The standard half-open fundamental domain for the action of $\mathrm{SL}_2(\mathbb{Z})$ on the
upper half-plane $\mathbb{H}$ by Möbius transformations is
$$F = \{\tau \in \mathbb{H} : \operatorname{re}\tau \in [-\tfrac12, \tfrac12),\ |\tau| \ge 1,
  \text{ and } |\tau| > 1 \text{ if } \operatorname{re}\tau > 0\}.$$
This file proves that every orbit meets $F$ in exactly one point
(`ModularGroup.exists_smul_mem_halfOpen_and_eq`), deducing it from Mathlib's closed fundamental
domain `ModularGroup.fd` and its classification `ModularGroup.cases_of_mem_fd_smul_mem_fd` of the
pairs $z, g z$ that both lie in the closed domain.

The source is Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 15, Lemma 15.10.
-/

@[expose] public section

open Complex UpperHalfPlane

open scoped MatrixGroups Modular

namespace ModularGroup

/-- A point of the half-open domain lies in Mathlib's closed fundamental domain. -/
private lemma mem_fd_of_mem_halfOpen {z : ℍ}
    (hz : z.re ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) ∧ 1 ≤ ‖(z : ℂ)‖ ∧ (0 < z.re → 1 < ‖(z : ℂ)‖)) :
    z ∈ 𝒟 := by
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := hz
  refine ⟨?_, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  rw [normSq_eq_norm_sq]
  nlinarith

/-- The real part of `S • z` when `‖z‖ = 1`. -/
private lemma re_S_smul_of_norm_eq_one {z : ℍ} (h : ‖(z : ℂ)‖ = 1) : (S • z).re = -z.re := by
  have hn : normSq (z : ℂ) = 1 := by rw [normSq_eq_norm_sq, h, one_pow]
  rw [← UpperHalfPlane.coe_re, modular_S_smul, coe_mk, inv_re, normSq_neg, hn, div_one,
    neg_re, UpperHalfPlane.coe_re]

/-- The norm of `S • z` when `‖z‖ = 1`. -/
private lemma norm_S_smul_of_norm_eq_one {z : ℍ} (h : ‖(z : ℂ)‖ = 1) :
    ‖((S • z : ℍ) : ℂ)‖ = 1 := by
  rw [modular_S_smul, coe_mk, norm_inv, norm_neg, h, inv_one]

/-- `g` and `-g` act in the same way. -/
private lemma smul_eq_of_eq_or_eq_neg {g h : SL(2, ℤ)} (hg : g = h ∨ g = -h) (z : ℍ) :
    g • z = h • z := by
  rcases hg with rfl | rfl
  · rfl
  · exact SL_neg_smul _ _

/-- **Fundamental domain of the modular group.** Let
$$F = \{\tau \in \mathbb{H} : \operatorname{re}\tau \in [-\tfrac12, \tfrac12),\ |\tau| \ge 1,
  \text{ and } (\operatorname{re}\tau > 0 \Rightarrow |\tau| > 1)\},$$
with $\mathrm{SL}_2(\mathbb{Z})$ acting on the upper half-plane $\mathbb{H}$ by Möbius
transformations. For every $\tau \in \mathbb{H}$:

1. there is $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ with $\gamma\tau \in F$; and
2. for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, if $\tau \in F$ and $\gamma\tau \in F$, then
   $\gamma\tau = \tau$.

So every $\mathrm{SL}_2(\mathbb{Z})$-orbit in $\mathbb{H}$ contains exactly one point of $F$.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 15, Lemma 15.10. Written out here is the reduction from Mathlib's closed
fundamental domain `ModularGroup.fd`: existence moves a point of the closed domain on its
boundary into $F$ by $T^{-1}$ or $S$, and uniqueness runs through Mathlib's classification
`ModularGroup.cases_of_mem_fd_smul_mem_fd` of the elements $g$ with $z, gz$ both in the closed
domain. The maximal-imaginary-part argument of the source is Mathlib's
`ModularGroup.exists_smul_mem_fd`. -/
theorem exists_smul_mem_halfOpen_and_eq (τ : ℍ) :
    (∃ γ : SL(2, ℤ), (γ • τ).re ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) ∧ 1 ≤ ‖((γ • τ : ℍ) : ℂ)‖ ∧
        (0 < (γ • τ).re → 1 < ‖((γ • τ : ℍ) : ℂ)‖)) ∧
      ∀ γ : SL(2, ℤ),
        (τ.re ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) ∧ 1 ≤ ‖(τ : ℂ)‖ ∧ (0 < τ.re → 1 < ‖(τ : ℂ)‖)) →
        ((γ • τ).re ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) ∧ 1 ≤ ‖((γ • τ : ℍ) : ℂ)‖ ∧
          (0 < (γ • τ).re → 1 < ‖((γ • τ : ℍ) : ℂ)‖)) → γ • τ = τ := by
  refine ⟨?_, fun g hz hgz => ?_⟩
  · obtain ⟨g, hg⟩ := exists_smul_mem_fd τ
    set w := g • τ with hw
    obtain ⟨hn, hre⟩ := hg
    rw [normSq_eq_norm_sq] at hn
    have hn1 : 1 ≤ ‖(w : ℂ)‖ := by nlinarith [norm_nonneg (w : ℂ)]
    obtain ⟨hre1, hre2⟩ := abs_le.mp hre
    rcases eq_or_lt_of_le hre2 with h | h
    · -- `re w = 1 / 2`: move by `T⁻¹`
      refine ⟨T⁻¹ * g, ?_⟩
      rw [mul_smul, ← hw]
      have hre' : (T⁻¹ • w).re = -(1 / 2) := by rw [re_T_inv_smul, h]; norm_num
      have hnorm : ‖((T⁻¹ • w : ℍ) : ℂ)‖ = ‖(w : ℂ)‖ := by
        have him : (T⁻¹ • w).im = w.im := im_T_inv_smul w
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq,
          ← normSq_eq_norm_sq, normSq_apply, normSq_apply, UpperHalfPlane.coe_re,
          UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im, hre', him, h]
        ring
      refine ⟨⟨by rw [hre'], by rw [hre']; norm_num⟩, by rw [hnorm]; exact hn1, ?_⟩
      intro hpos
      rw [hre'] at hpos
      norm_num at hpos
    · by_cases hS : 0 < w.re ∧ ‖(w : ℂ)‖ = 1
      · -- `re w ∈ (0, 1 / 2)` on the unit circle: move by `S`
        refine ⟨S * g, ?_⟩
        rw [mul_smul, ← hw, re_S_smul_of_norm_eq_one hS.2, norm_S_smul_of_norm_eq_one hS.2]
        refine ⟨⟨by linarith, by linarith [hS.1]⟩, le_rfl, fun hpos => ?_⟩
        linarith [hS.1]
      · refine ⟨g, ⟨hre1, h⟩, hn1, fun hpos => ?_⟩
        exact lt_of_le_of_ne hn1 fun he => hS ⟨hpos, he.symm⟩
  · have hz' := mem_fd_of_mem_halfOpen hz
    have hgz' := mem_fd_of_mem_halfOpen hgz
    obtain ⟨⟨hz1, hz2⟩, hz3, hz4⟩ := hz
    obtain ⟨⟨hgz1, hgz2⟩, hgz3, hgz4⟩ := hgz
    have hTρ : (T • ρ).re = 1 / 2 := by rw [re_T_smul]; norm_num [ρ]
    have hρre : ((1 : ℝ) +ᵥ ρ : ℍ).re = 1 / 2 := by rw [vadd_re]; norm_num [ρ]
    rcases cases_of_mem_fd_smul_mem_fd hz' hgz' with
      h | ⟨h, hre⟩ | ⟨h, hre⟩ | ⟨h, hn⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ |
        ⟨h, rfl⟩
    · rw [smul_eq_of_eq_or_eq_neg h, one_smul]
    · -- `±T`: then `re (g • z) = 1 / 2`
      have : (g • τ).re = 1 / 2 := by
        rw [smul_eq_of_eq_or_eq_neg h, re_T_smul, hre]
        norm_num
      linarith
    · linarith
    · -- `±S` on the unit circle: then `re z = 0`, so `z = I`
      have hgS : g • τ = S • τ := smul_eq_of_eq_or_eq_neg h τ
      rw [hgS] at hgz4 hgz3 ⊢
      rw [re_S_smul_of_norm_eq_one hn, norm_S_smul_of_norm_eq_one hn] at hgz4
      have h0 : τ.re = 0 := by
        rcases lt_trichotomy τ.re 0 with h | h | h
        · exact absurd (hgz4 (by linarith)) (lt_irrefl _)
        · exact h
        · exact absurd (hz4 h) (by rw [hn]; exact lt_irrefl _)
      have hI : τ = UpperHalfPlane.I := by
        have hn2 : normSq (τ : ℂ) = 1 := by rw [normSq_eq_norm_sq, hn, one_pow]
        rw [normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, h0] at hn2
        have him : τ.im = 1 := by nlinarith [τ.im_pos]
        ext
        apply Complex.ext <;> simp [h0, him]
      subst hI
      exact stabilizer_I.mpr (by simp)
    · linarith
    · linarith
    · linarith
    · -- `±ST` fixes `ρ`
      rw [smul_eq_of_eq_or_eq_neg h]
      exact stabilizer_ρ.mpr (by simp)
    · -- `±TST` sends `ρ` to `1 + ρ`
      have : (g • ρ).re = 1 / 2 := by
        have hST : (S * T) • ρ = ρ := stabilizer_ρ.mpr (by simp)
        rw [smul_eq_of_eq_or_eq_neg h, mul_assoc, mul_smul, hST, hTρ]
      linarith
    · -- `±T⁻¹S` fixes `ρ`
      rw [smul_eq_of_eq_or_eq_neg h]
      exact stabilizer_ρ.mpr (by simp)

end ModularGroup
