/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Real.Sqrt

@[expose] public section

/-! # Projected subgradient method: the `D G / √T` rate

The projected subgradient method with constant step
`η = D / (G √T)` and averaged iterates achieves
`f x̄ - f* ≤ D G / √T` for a convex objective with subgradients
bounded by `G`. This is the deterministic core of roadmap package
ML-21 of the Atlas TCS canon roadmap (the stochastic version takes
expectations of the same one-step estimate).

Source: Boyd and Vandenberghe, Convex Optimization (2004),
Section 9.3; Shalev-Shwartz and Ben-David (2014), Chapter 13.
-/

open Finset

/-- The projected subgradient method iterates, with constant step
size `η`: project the subgradient step from the previous iterate. -/
noncomputable def sgdIter {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (g : ℕ → E → E) (η : ℝ) (x0 : E) : ℕ → E
  | 0 => x0
  | t + 1 => proj (sgdIter proj g η x0 t - η • g t (sgdIter proj g η x0 t))

/-- One step of the projected subgradient method: nonexpansiveness of the
projection, the subgradient inequality and the gradient bound. -/
private theorem sgd_onestep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {proj : E → E} {f : E → ℝ} {G η : ℝ}
    (hη : 0 < η)
    (hproj : ∀ u v, ‖proj u - proj v‖ ≤ ‖u - v‖)
    (xstar : E) (hprojstar : proj xstar = xstar)
    (x gt : E) (hsubx : f x + inner ℝ gt (xstar - x) ≤ f xstar)
    (hgx : ‖gt‖ ≤ G) :
    ‖proj (x - η • gt) - xstar‖ ^ 2
      ≤ ‖x - xstar‖ ^ 2 - 2 * η * (f x - f xstar) + η ^ 2 * G ^ 2 := by
  have hG0 : (0 : ℝ) ≤ G := le_trans (norm_nonneg gt) hgx
  have hnonexp : ‖proj (x - η • gt) - xstar‖ ≤ ‖(x - η • gt) - xstar‖ := by
    have h := hproj (x - η • gt) xstar
    rwa [hprojstar] at h
  have hneg : -(‖(x - η • gt) - xstar‖) ≤ ‖proj (x - η • gt) - xstar‖ :=
    le_trans (neg_nonpos.mpr (norm_nonneg _)) (norm_nonneg _)
  have hsq : ‖proj (x - η • gt) - xstar‖ ^ 2 ≤ ‖(x - η • gt) - xstar‖ ^ 2 :=
    sq_le_sq' hneg hnonexp
  have hexp : ‖(x - η • gt) - xstar‖ ^ 2
      = ‖x - xstar‖ ^ 2 - 2 * η * inner ℝ gt (x - xstar) + η ^ 2 * ‖gt‖ ^ 2 := by
    have h1 : (x - η • gt) - xstar = (x - xstar) - η • gt := by abel
    have h2 : inner ℝ (x - xstar) (η • gt) = η * inner ℝ gt (x - xstar) := by
      rw [inner_smul_right, real_inner_comm gt (x - xstar)]
    have h3 : ‖η • gt‖ ^ 2 = η ^ 2 * ‖gt‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
      ring
    rw [h1, norm_sub_sq_real, h2, h3]
    ring
  have hsub' : f x - f xstar ≤ inner ℝ gt (x - xstar) := by
    have hid : inner ℝ gt (xstar - x) = -inner ℝ gt (x - xstar) := by
      simp only [inner_sub_right]
      ring
    rw [hid] at hsubx
    linarith
  have hgsq : ‖gt‖ ^ 2 ≤ G ^ 2 :=
    sq_le_sq' (le_trans (neg_nonpos.mpr hG0) (norm_nonneg _)) hgx
  have e1 :=
    mul_le_mul_of_nonneg_left hsub' (show (0 : ℝ) ≤ 2 * η from mul_nonneg zero_le_two hη.le)
  have e2 := mul_le_mul_of_nonneg_left hgsq (show (0 : ℝ) ≤ η ^ 2 from sq_nonneg η)
  linarith

/-- Jensen for the uniform average, from binary convexity. -/
private theorem sgd_jensen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ}
    (hconv : ∀ x y : E, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ a * f x + b * f y)
    (p : ℕ → E) {T : ℕ} (hT : 0 < T) :
    f ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, p t)
      ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (p t) := by
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  have hConvex : ConvexOn ℝ Set.univ f := ⟨convex_univ, fun x _ y _ a b ha hb hab => by
    simpa only [smul_eq_mul] using hconv x y a b ha hb hab⟩
  have h₀ : ∀ i ∈ Finset.range T, 0 ≤ (fun _ => (T : ℝ)⁻¹) i :=
    fun i _ => inv_nonneg.mpr hTpos.le
  have h₁ : ∑ i ∈ Finset.range T, (fun _ => (T : ℝ)⁻¹) i = 1 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hTne]
  have hmem : ∀ i ∈ Finset.range T, (fun t => p t) i ∈ Set.univ :=
    fun i _ => Set.mem_univ _
  have h := hConvex.map_sum_le (t := Finset.range T) (w := fun _ => (T : ℝ)⁻¹)
    (p := fun t => p t) h₀ h₁ hmem
  simp only [← Finset.smul_sum] at h
  simp only [smul_eq_mul] at h
  exact h

/-- The `D G / √T` rate of the projected subgradient method: for a
convex objective (subgradient inequality) with subgradients bounded
by `G`, a nonexpansive projection fixing `xstar`, and
`‖x0 - xstar‖ ≤ D`, the average iterate `x̄` after `T` steps with
step `η = D / (G √T)` satisfies `f x̄ - f xstar ≤ D G / √T`. -/
theorem sgd_rate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {proj : E → E} {f : E → ℝ} {g : ℕ → E → E} {D G : ℝ}
    (hD : 0 < D) (hG : 0 < G)
    (hproj : ∀ u v, ‖proj u - proj v‖ ≤ ‖u - v‖)
    (xstar : E) (hprojstar : proj xstar = xstar)
    (hsub : ∀ (t : ℕ) (x : E), f x + @inner ℝ E _ (g t x) (xstar - x) ≤ f xstar)
    (hg : ∀ (t : ℕ) (x : E), ‖g t x‖ ≤ G)
    (hconv : ∀ x y : E, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ a * f x + b * f y)
    (x0 : E) (hdist : ‖x0 - xstar‖ ≤ D) {T : ℕ} (hT : 0 < T) :
    f ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, sgdIter proj g (D / (G * Real.sqrt T)) x0 t)
      - f xstar ≤ D * G / Real.sqrt T := by
  set η : ℝ := D / (G * Real.sqrt T) with hηdef
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hsqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  have hsqrt_ne : Real.sqrt T ≠ 0 := ne_of_gt hsqrt_pos
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  have hGne : G ≠ 0 := ne_of_gt hG
  have hη : 0 < η := by
    rw [hηdef]
    exact div_pos hD (mul_pos hG hsqrt_pos)
  have h2η : (0 : ℝ) < 2 * η := mul_pos (by norm_num) hη
  have h2ηne : (2 : ℝ) * η ≠ 0 := ne_of_gt h2η
  have hηG : η * G * Real.sqrt T = D := by
    rw [hηdef]
    have hgne : G * Real.sqrt T ≠ 0 := mul_ne_zero hGne hsqrt_ne
    calc D / (G * Real.sqrt T) * G * Real.sqrt T
        = D / (G * Real.sqrt T) * (G * Real.sqrt T) := by ring
      _ = D := div_mul_cancel₀ D hgne
  have hsqT : (Real.sqrt T) ^ 2 = (T : ℝ) := Real.sq_sqrt (Nat.cast_nonneg T)
  have hηsq : η ^ 2 * G ^ 2 * (T : ℝ) = D ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hηG
    rw [mul_pow, mul_pow, hsqT] at h
    linear_combination h
  have hstep : ∀ t : ℕ, 2 * η * (f (sgdIter proj g η x0 t) - f xstar)
      ≤ (‖sgdIter proj g η x0 t - xstar‖ ^ 2
          - ‖sgdIter proj g η x0 (t + 1) - xstar‖ ^ 2) + η ^ 2 * G ^ 2 := by
    intro t
    have h := sgd_onestep hη hproj xstar hprojstar _ _
      (hsub t (sgdIter proj g η x0 t)) (hg t (sgdIter proj g η x0 t))
    rw [show sgdIter proj g η x0 (t + 1)
        = proj (sgdIter proj g η x0 t - η • g t (sgdIter proj g η x0 t)) from rfl]
    linarith
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range T) => hstep t)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_range_sub',
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [show sgdIter proj g η x0 0 = x0 from rfl] at hsum
  have hD0 : ‖x0 - xstar‖ ^ 2 ≤ D ^ 2 :=
    sq_le_sq' (le_trans (neg_nonpos.mpr hD.le) (norm_nonneg _)) hdist
  have hDT : (0 : ℝ) ≤ ‖sgdIter proj g η x0 T - xstar‖ ^ 2 := sq_nonneg _
  have hS_le : (∑ t ∈ Finset.range T, (f (sgdIter proj g η x0 t) - f xstar))
      ≤ (D ^ 2 + (T : ℝ) * η ^ 2 * G ^ 2) / (2 * η) := by
    rw [le_div_iff₀ h2η]
    linarith
  have hTT : (T : ℝ) * η ^ 2 * G ^ 2 = D ^ 2 := by linear_combination hηsq
  have hfinal : (D ^ 2 + (T : ℝ) * η ^ 2 * G ^ 2) / (2 * η)
      = D * G * Real.sqrt T := by
    rw [hTT, div_eq_iff h2ηne]
    linear_combination (-2 * D) * hηG
  have hS_DG : (∑ t ∈ Finset.range T, (f (sgdIter proj g η x0 t) - f xstar))
      ≤ D * G * Real.sqrt T :=
    le_trans hS_le (le_of_eq hfinal)
  have hJ := sgd_jensen hconv (fun t => sgdIter proj g η x0 t) hT
  have havg : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (sgdIter proj g η x0 t) - f xstar
      = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (f (sgdIter proj g η x0 t) - f xstar) := by
    have hTc : (T : ℝ)⁻¹ * ((T : ℝ) * f xstar) = f xstar := by
      rw [← mul_assoc, inv_mul_cancel₀ hTne, one_mul]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_sub, hTc]
  have hmul := mul_le_mul_of_nonneg_left hS_DG (inv_nonneg.mpr hTpos.le)
  have hlast : (T : ℝ)⁻¹ * (D * G * Real.sqrt T) = D * G / Real.sqrt T := by
    have hss : Real.sqrt T * Real.sqrt T = (T : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg T)
    have hinv : (T : ℝ)⁻¹ * (T : ℝ) = 1 := inv_mul_cancel₀ hTne
    rw [eq_div_iff hsqrt_ne]
    calc (T : ℝ)⁻¹ * (D * G * Real.sqrt T) * Real.sqrt T
        = (T : ℝ)⁻¹ * (D * G * (Real.sqrt T * Real.sqrt T)) := by ring
      _ = (T : ℝ)⁻¹ * (D * G * (T : ℝ)) := by rw [hss]
      _ = D * G * ((T : ℝ)⁻¹ * (T : ℝ)) := by ring
      _ = D * G := by rw [hinv, mul_one]
  calc f ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, sgdIter proj g η x0 t) - f xstar
      ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (sgdIter proj g η x0 t) - f xstar :=
        sub_le_sub_right hJ (f xstar)
    _ = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (f (sgdIter proj g η x0 t) - f xstar) := havg
    _ ≤ (T : ℝ)⁻¹ * (D * G * Real.sqrt T) := hmul
    _ = D * G / Real.sqrt T := hlast
