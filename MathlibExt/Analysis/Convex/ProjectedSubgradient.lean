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
public import MathlibExt.Analysis.Convex.OnlineGradientDescent

@[expose] public section

/-! # Projected subgradient method: the `D G / √T` rate

The projected subgradient method with constant step
`η = D / (G √T)` and averaged iterates achieves
`f x̄ - f* ≤ D G / √T` for a convex objective with subgradients
bounded by `G`. This is the deterministic core of roadmap package
ML-21 of the Atlas TCS canon roadmap (the stochastic version takes
expectations of the same one-step estimate).

The iterates are the projected online gradient descent iterates
`ogdIter` from `MathlibExt.Analysis.Convex.OnlineGradientDescent`, and
the rate is derived from its regret theorem `ogd_regret` with the
constant round cost `fun _ => f`; there is no second public iterator
definition. The subgradient hypothesis is quantified over every
comparison point `y`, so `g t x` is genuinely a subgradient of `f` at
`x`; it is specialized to the comparator `xstar` in the proof, as
`ogd_regret` requires.

Source: Boyd and Vandenberghe, Convex Optimization (2004),
Section 9.3; Shalev-Shwartz and Ben-David (2014), Chapter 13.
-/

open Finset

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
convex objective with subgradients bounded by `G` (the subgradient
inequality quantified over every comparison point `y`), a
nonexpansive projection fixing `xstar`, and `‖x0 - xstar‖ ≤ D`, the
average iterate `x̄` after `T` steps with step `η = D / (G √T)`
satisfies `f x̄ - f xstar ≤ D G / √T`. The summed objective bound is
`ogd_regret` at the constant round cost `fun _ => f`, with the
subgradient inequality specialized to `xstar`. -/
theorem sgd_rate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {proj : E → E} {f : E → ℝ} {g : ℕ → E → E} {D G : ℝ}
    (hD : 0 < D) (hG : 0 < G)
    (hproj : ∀ u v, ‖proj u - proj v‖ ≤ ‖u - v‖)
    (xstar : E) (hprojstar : proj xstar = xstar)
    (hsub : ∀ (t : ℕ) (x y : E), f x + @inner ℝ E _ (g t x) (y - x) ≤ f y)
    (hg : ∀ (t : ℕ) (x : E), ‖g t x‖ ≤ G)
    (hconv : ∀ x y : E, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ a * f x + b * f y)
    (x0 : E) (hdist : ‖x0 - xstar‖ ≤ D) {T : ℕ} (hT : 0 < T) :
    f ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, ogdIter proj g (D / (G * Real.sqrt T)) x0 t)
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
  -- The norm-nonexpansiveness hypothesis is `LipschitzWith 1 proj`, the
  -- form `ogd_regret` takes.
  have hLip : LipschitzWith 1 proj := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro u v
    have h := hproj u v
    rw [dist_eq_norm, dist_eq_norm]
    simpa using h
  -- Specialize the quantified subgradient inequality to `xstar`.
  have hsub_star : ∀ (t : ℕ) (x : E),
      (fun _ => f) t x + @inner ℝ E _ (g t x) (xstar - x) ≤ (fun _ => f) t xstar :=
    fun t x => hsub t x xstar
  have hreg : (∑ t ∈ Finset.range T, (f (ogdIter proj g η x0 t) - f xstar)) ≤
      ‖x0 - xstar‖ ^ 2 / (2 * η) +
        (η / 2) * ∑ t ∈ Finset.range T, ‖g t (ogdIter proj g η x0 t)‖ ^ 2 :=
    ogd_regret (f := fun _ => f) hη hLip xstar hprojstar hsub_star x0 T
  have hG0 : (0 : ℝ) ≤ G := le_trans (norm_nonneg _) (hg 0 x0)
  have hgsum : (∑ t ∈ Finset.range T, ‖g t (ogdIter proj g η x0 t)‖ ^ 2)
      ≤ (T : ℝ) * G ^ 2 := by
    have h1 : ∀ t ∈ Finset.range T, ‖g t (ogdIter proj g η x0 t)‖ ^ 2 ≤ G ^ 2 := by
      intro t _
      exact sq_le_sq' (le_trans (neg_nonpos.mpr hG0) (norm_nonneg _)) (hg t _)
    calc ∑ t ∈ Finset.range T, ‖g t (ogdIter proj g η x0 t)‖ ^ 2
        ≤ ∑ _t ∈ Finset.range T, G ^ 2 := Finset.sum_le_sum h1
      _ = (T : ℝ) * G ^ 2 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hD0 : ‖x0 - xstar‖ ^ 2 ≤ D ^ 2 :=
    sq_le_sq' (le_trans (neg_nonpos.mpr hD.le) (norm_nonneg _)) hdist
  have hEq : D ^ 2 / (2 * η) + (η / 2) * ((T : ℝ) * G ^ 2) = D * G * Real.sqrt T := by
    have hηne : η ≠ 0 := ne_of_gt hη
    field_simp
    linear_combination hηsq - 2 * D * hηG
  have hS_DG : (∑ t ∈ Finset.range T, (f (ogdIter proj g η x0 t) - f xstar))
      ≤ D * G * Real.sqrt T := by
    have h1 : ‖x0 - xstar‖ ^ 2 / (2 * η) ≤ D ^ 2 / (2 * η) := by gcongr
    have h2 : (η / 2) * ∑ t ∈ Finset.range T, ‖g t (ogdIter proj g η x0 t)‖ ^ 2
        ≤ (η / 2) * ((T : ℝ) * G ^ 2) := by gcongr
    calc (∑ t ∈ Finset.range T, (f (ogdIter proj g η x0 t) - f xstar))
        ≤ ‖x0 - xstar‖ ^ 2 / (2 * η) +
            (η / 2) * ∑ t ∈ Finset.range T, ‖g t (ogdIter proj g η x0 t)‖ ^ 2 := hreg
      _ ≤ D ^ 2 / (2 * η) + (η / 2) * ((T : ℝ) * G ^ 2) := add_le_add h1 h2
      _ = D * G * Real.sqrt T := hEq
  have hJ := sgd_jensen hconv (fun t => ogdIter proj g η x0 t) hT
  have havg : (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (ogdIter proj g η x0 t) - f xstar
      = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (f (ogdIter proj g η x0 t) - f xstar) := by
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
  calc f ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, ogdIter proj g η x0 t) - f xstar
      ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, f (ogdIter proj g η x0 t) - f xstar :=
        sub_le_sub_right hJ (f xstar)
    _ = (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (f (ogdIter proj g η x0 t) - f xstar) := havg
    _ ≤ (T : ℝ)⁻¹ * (D * G * Real.sqrt T) := hmul
    _ = D * G / Real.sqrt T := hlast
