/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.ParallelogramArgumentPrinciple

/-!
# Tests for the argument principle for a parallelogram

Compile-time examples exercising `MeromorphicOn.parallelogramBoundaryIntegral_logDeriv` and its
companions: the function `z - w` with one zero inside, its reciprocal with one pole inside, the
boundary integral of `1 / (z - w)` over the unit square, Cauchy's theorem for a polynomial, and the
consequence for an elliptic function that its orders in a period parallelogram whose boundary
avoids its zeros and poles add up to zero.
-/

@[expose] public section

open Complex Set
open scoped Real

/-- The order of `z - w` at a point other than `w` is `0`. -/
private theorem meromorphicOrderAt_sub_const_of_ne {w P : ℂ} (h : P ≠ w) :
    meromorphicOrderAt (fun z : ℂ => z - w) P = 0 := by
  rw [AnalyticAt.meromorphicOrderAt_eq (by fun_prop),
    (analyticOrderAt_eq_zero (f := fun z : ℂ => z - w)).2 (Or.inr (sub_ne_zero.2 h))]
  rfl

/-- `z - w` has a single zero, of order `1`, inside a positively oriented parallelogram around `w`,
so the boundary integral of its logarithmic derivative is `2πi`. -/
example {z₀ ω₁ ω₂ w : ℂ} (hω : 0 < (ω₂ / ω₁).im)
    (hw : ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ w = z₀ + t₁ • ω₁ + t₂ • ω₂) :
    parallelogramBoundaryIntegral (logDeriv fun z => z - w) z₀ ω₁ ω₂ = 2 * π * I := by
  set D := {P : ℂ | ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ P = z₀ + t₁ • ω₁ + t₂ • ω₂}
  have hwD : w ∈ D := hw
  obtain ⟨-, h⟩ := MeromorphicOn.parallelogramBoundaryIntegral_logDeriv_of_im_pos isOpen_univ
    (f := fun z => z - w) (z₀ := z₀)
    (fun z _ => (analyticAt_id.sub analyticAt_const).meromorphicAt) hω (subset_univ _)
    (fun P _ hP => meromorphicOrderAt_sub_const_of_ne fun hPw => hP (by rw [hPw]; exact hwD))
  have hsupp : D ∩ Function.support (fun P => (meromorphicOrderAt (fun z : ℂ => z - w) P).untop₀) =
      {w} := by
    ext P
    simp only [mem_inter_iff, Function.mem_support, mem_singleton_iff]
    constructor
    · rintro ⟨-, hP⟩
      by_contra hPw
      exact hP (by rw [meromorphicOrderAt_sub_const_of_ne hPw]; rfl)
    · rintro rfl
      exact ⟨hwD, by rw [meromorphicOrderAt_id_sub_const]; decide⟩
  rw [h, ← finsum_mem_inter_support, hsupp, finsum_mem_singleton, meromorphicOrderAt_id_sub_const]
  simp

/-- `1 / (z - w)` has a single pole, of order `1`, inside a negatively oriented parallelogram
around `w`, so the boundary integral of its logarithmic derivative is `(-1) · 2πi · (-1) = 2πi`. -/
example {z₀ ω₁ ω₂ w : ℂ} (hω : (ω₂ / ω₁).im < 0)
    (hw : ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ w = z₀ + t₁ • ω₁ + t₂ • ω₂) :
    parallelogramBoundaryIntegral (logDeriv fun z => (z - w)⁻¹) z₀ ω₁ ω₂ = 2 * π * I := by
  set D := {P : ℂ | ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ P = z₀ + t₁ • ω₁ + t₂ • ω₂}
  have hwD : w ∈ D := hw
  have hord : ∀ P, meromorphicOrderAt (fun z : ℂ => (z - w)⁻¹) P =
      -meromorphicOrderAt (fun z : ℂ => z - w) P := fun P =>
    meromorphicOrderAt_inv
  obtain ⟨-, h⟩ := MeromorphicOn.parallelogramBoundaryIntegral_logDeriv isOpen_univ
    (f := fun z => (z - w)⁻¹) (z₀ := z₀)
    (fun z _ => (analyticAt_id.sub analyticAt_const).meromorphicAt.inv) hω.ne (subset_univ _)
    (fun P _ hP => by
      rw [hord, meromorphicOrderAt_sub_const_of_ne fun hPw => hP (by rw [hPw]; exact hwD),
        neg_zero])
  have hsupp : D ∩ Function.support
      (fun P => (meromorphicOrderAt (fun z : ℂ => (z - w)⁻¹) P).untop₀) = {w} := by
    ext P
    simp only [mem_inter_iff, Function.mem_support, mem_singleton_iff]
    constructor
    · rintro ⟨-, hP⟩
      by_contra hPw
      exact hP (by rw [hord, meromorphicOrderAt_sub_const_of_ne hPw, neg_zero]; rfl)
    · rintro rfl
      exact ⟨hwD, by rw [hord, meromorphicOrderAt_id_sub_const]; decide⟩
  have hn : ¬ 0 < (ω₂ / ω₁).im := not_lt.2 hω.le
  rw [h, ← finsum_mem_inter_support, hsupp, finsum_mem_singleton, hord,
    meromorphicOrderAt_id_sub_const, show (-(1 : WithTop ℤ)).untop₀ = -1 from rfl]
  simp only [hn, ↓reduceIte]
  push_cast
  ring

/-- The boundary of the unit square with vertex `0` winds once around its centre. -/
example : parallelogramBoundaryIntegral (fun z => (z - (1 + I) / 2)⁻¹) 0 1 I = 2 * π * I := by
  rw [parallelogramBoundaryIntegral_inv_sub (by simp) ⟨1 / 2, 1 / 2, by norm_num, by norm_num,
    by norm_num, by norm_num, by simp only [Complex.real_smul]; push_cast; ring⟩]
  simp

/-- Cauchy's theorem: the boundary integral of `z²` over any nondegenerate parallelogram is `0`. -/
example {z₀ ω₁ ω₂ : ℂ} (hω : (ω₂ / ω₁).im ≠ 0) :
    parallelogramBoundaryIntegral (fun z => z ^ 2) z₀ ω₁ ω₂ = 0 :=
  parallelogramBoundaryIntegral_eq_zero_of_differentiableOn isOpen_univ
    (fun _ _ => (differentiableAt_pow 2).differentiableWithinAt) hω (subset_univ _)

namespace PeriodPair

/-- For an elliptic function `f` with no zero or pole on the boundary of the period parallelogram
with vertex `z₀`, the orders of `f` in the open parallelogram add up to `0`: the boundary integral
of the elliptic function `f' / f` vanishes, as opposite sides cancel. -/
example (L : PeriodPair) {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) (z₀ : ℂ)
    (hbd : ∀ P ∈ {P | ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧
        P = z₀ + t₁ • L.ω₁ + t₂ • L.ω₂},
      P ∉ {P | ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ P = z₀ + t₁ • L.ω₁ + t₂ • L.ω₂} →
        meromorphicOrderAt f P = 0) :
    ∑ᶠ P ∈ {P | ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧
      P = z₀ + t₁ • L.ω₁ + t₂ • L.ω₂}, (meromorphicOrderAt f P).untop₀ = 0 := by
  obtain ⟨-, h⟩ := MeromorphicOn.parallelogramBoundaryIntegral_logDeriv isOpen_univ
    (fun z _ => hf.meromorphic z) L.im_ω₂_div_ω₁_ne_zero (subset_univ _) hbd
  rw [hf.logDeriv.periodic.parallelogramBoundaryIntegral_eq_zero z₀] at h
  have hσ : (if 0 < (L.ω₂ / L.ω₁).im then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
  exact_mod_cast (mul_eq_zero.1 h.symm).resolve_left (mul_ne_zero two_pi_I_ne_zero hσ)

end PeriodPair
