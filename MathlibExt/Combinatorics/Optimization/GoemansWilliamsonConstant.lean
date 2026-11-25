/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The Goemans–Williamson constant

The constant `α = min_{0 < θ ≤ π} (2 / π) · θ / (1 - cos θ)` of M. X. Goemans and
D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability
problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145, §2 and §3.

* `gwConstant_mul_le` and `gwConstant_mul_le_arccos_div_pi` are their Lemma 3.4: for
  `θ ∈ [0, π]`, `α · (1 - cos θ) / 2 ≤ θ / π`; equivalently `arccos y / π ≥ α (1 - y) / 2`
  for `-1 ≤ y ≤ 1`.
* `lt_gwConstant` is their Lemma 3.5, `α > 0.87856`, proved along their argument: on
  `[0, π / 2]` the chord bound `1 - cos θ ≤ 2θ / π`; on `[π / 2, π]` the tangent line of the
  concave function `1 - cos` at a point `θ₀ = π - φ` to the left of the minimiser, here
  `φ = 0.810472`, with certified Taylor bounds for `sin φ` and `cos φ`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Optimization.GoemansWilliamson

open Real Set

/-! ### Certified Taylor bounds for `sin` and `cos` on `[0, ∞)` -/

private theorem le_of_hasDerivAt_le {f g f' g' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (h0 : f 0 ≤ g 0) (hd : ∀ x, 0 ≤ x → f' x ≤ g' x) {x : ℝ} (hx : 0 ≤ x) : f x ≤ g x := by
  have hmono : MonotoneOn (fun t => g t - f t) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun t => g' t - f' t)
    · exact (continuous_iff_continuousAt.2 fun t =>
        ((hg t).sub (hf t)).continuousAt).continuousOn
    · intro t _
      exact ((hg t).sub (hf t)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact sub_nonneg.2 (hd t (le_of_lt ht))
  have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
  simp only at this
  linarith

private theorem cos_le_four {x : ℝ} (hx : 0 ≤ x) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  refine le_of_hasDerivAt_le (f := cos) (g := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24)
    (f' := fun t => -sin t) (g' := fun t => -t + t ^ 3 / 6)
    (fun t => hasDerivAt_cos t) (fun t => ?_) (by simp) (fun t ht => ?_) hx
  · have h := (((hasDerivAt_pow 2 t).div_const 2).neg.add
      ((hasDerivAt_pow 4 t).div_const 24)).const_add 1
    convert h using 1
    · funext s; simp only [Pi.neg_apply, Pi.add_apply]; ring
    · push_cast; ring
  · have := sin_ge_sub_cube ht
    linarith

private theorem sin_le_five {x : ℝ} (hx : 0 ≤ x) :
    sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  refine le_of_hasDerivAt_le (f := sin) (g := fun t => t - t ^ 3 / 6 + t ^ 5 / 120)
    (f' := fun t => cos t) (g' := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24)
    (fun t => hasDerivAt_sin t) (fun t => ?_) (by simp) (fun t ht => cos_le_four ht) hx
  have h := ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
    ((hasDerivAt_pow 5 t).div_const 120)
  convert h using 1
  · funext s; simp
  · simp; ring

private theorem cos_ge_six {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ cos x := by
  refine le_of_hasDerivAt_le (g := cos)
    (f := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) (g' := fun t => -sin t)
    (f' := fun t => -t + t ^ 3 / 6 - t ^ 5 / 120)
    (fun t => ?_) (fun t => hasDerivAt_cos t) (by simp) (fun t ht => ?_) hx
  · have h := ((((hasDerivAt_pow 2 t).div_const 2).neg.add
      ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).const_add 1
    convert h using 1
    · funext s; simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]; ring
    · push_cast; ring
  · have := sin_le_five ht
    linarith

private theorem sin_ge_seven {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ sin x := by
  refine le_of_hasDerivAt_le (g := sin)
    (f := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040) (g' := fun t => cos t)
    (f' := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)
    (fun t => ?_) (fun t => hasDerivAt_sin t) (by simp) (fun t ht => cos_ge_six ht) hx
  have h := (((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
    ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)
  convert h using 1
  · funext s; simp
  · simp; ring

private theorem cos_le_eight {x : ℝ} (hx : 0 ≤ x) :
    cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  refine le_of_hasDerivAt_le (f := cos)
    (g := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320)
    (f' := fun t => -sin t)
    (g' := fun t => -t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040)
    (fun t => hasDerivAt_cos t) (fun t => ?_) (by simp) (fun t ht => ?_) hx
  · have h := (((((hasDerivAt_pow 2 t).div_const 2).neg.add
      ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add
      ((hasDerivAt_pow 8 t).div_const 40320)).const_add 1
    convert h using 1
    · funext s; simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]; ring
    · push_cast; ring
  · have := sin_ge_seven ht
    linarith

private theorem sin_le_nine {x : ℝ} (hx : 0 ≤ x) :
    sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 := by
  refine le_of_hasDerivAt_le (f := sin)
    (g := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880)
    (f' := fun t => cos t)
    (g' := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320)
    (fun t => hasDerivAt_sin t) (fun t => ?_) (by simp) (fun t ht => cos_le_eight ht) hx
  have h := ((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
    ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add
    ((hasDerivAt_pow 9 t).div_const 362880)
  convert h using 1
  · funext s; simp
  · simp; ring

/-! ### The tangent-line bound on `[π / 2, π]` -/

/-- Tangent line of the convex function `cos` on `[π / 2, π]` at `π - φ`. -/
private theorem neg_cos_le_tangent {φ θ : ℝ} (hφ0 : 0 < φ) (hφ : φ < π / 2)
    (hθ0 : π / 2 ≤ θ) (hθ : θ ≤ π) :
    -cos θ ≤ cos φ + sin φ * (θ - (π - φ)) := by
  have hconc : ConcaveOn ℝ (Icc 0 π) sin := strictConcaveOn_sin_Icc.concaveOn
  set t := θ - π / 2 with ht
  set t₀ := π / 2 - φ with ht₀
  have hpi := pi_pos
  have htmem : t ∈ Icc 0 π := ⟨by linarith, by linarith⟩
  have ht₀mem : t₀ ∈ Icc 0 π := ⟨by linarith, by linarith⟩
  have hsin_t : sin t = -cos θ := by
    rw [ht, sin_sub_pi_div_two]
  have hsin_t₀ : sin t₀ = cos φ := by rw [ht₀, sin_pi_div_two_sub]
  have hcos_t₀ : cos t₀ = sin φ := by rw [ht₀, cos_pi_div_two_sub]
  have key : sin t ≤ sin t₀ + cos t₀ * (t - t₀) := by
    rcases lt_trichotomy t t₀ with h | h | h
    · have hs := hconc.le_slope_of_hasDerivAt htmem ht₀mem h (hasDerivAt_sin t₀)
      rw [slope_def_field, le_div_iff₀ (by linarith)] at hs
      nlinarith
    · rw [h]; simp
    · have hs := hconc.slope_le_of_hasDerivAt ht₀mem htmem h (hasDerivAt_sin t₀)
      rw [slope_def_field, div_le_iff₀ (by linarith)] at hs
      nlinarith
  rw [hsin_t, hsin_t₀, hcos_t₀] at key
  have : t - t₀ = θ - (π - φ) := by rw [ht, ht₀]; ring
  rw [this] at key
  exact key

/-! ### The certified numerical inequality -/

/-- **The Goemans–Williamson inequality with a certified constant.** For every
`θ ∈ [0, π]`, `0.878565 · (1 - cos θ) / 2 ≤ θ / π`. This is the numerical content of
Lemmas 3.4–3.5 of M. X. Goemans and D. P. Williamson, *J. ACM* 42(6) (1995), 1115–1145,
proved along their argument (chord on `[0, π / 2]`, tangent of `1 - cos` on `[π / 2, π]`). -/
theorem certified_mul_one_sub_cos_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ π) :
    (0.878565 : ℝ) * ((1 - cos θ) / 2) ≤ θ / π := by
  have hpi := pi_pos
  rcases le_or_gt θ (π / 2) with hle | hgt
  · -- chord bound `1 - cos θ ≤ 2θ / π`
    have hc := one_sub_mul_le_cos hθ0 hle
    have h1 : (1 - cos θ) / 2 ≤ θ / π := by
      rw [div_le_div_iff₀ (by norm_num) hpi]
      have : 2 / π * θ * π = 2 * θ := by field_simp
      nlinarith
    have hnn : 0 ≤ (1 - cos θ) / 2 := by have := cos_le_one θ; linarith
    nlinarith
  · obtain ⟨φ, hφdef⟩ : ∃ φ : ℝ, φ = 101309 / 125000 := ⟨_, rfl⟩
    have hφ0 : (0 : ℝ) ≤ φ := by norm_num [hφdef]
    have hπlo := pi_gt_d20
    have hπhi := pi_lt_d20
    have hφpi : φ < π / 2 := by linarith
    have hslo : (0.724612123616 : ℝ) ≤ sin φ := by
      have := sin_ge_seven hφ0
      rw [hφdef] at this ⊢
      norm_num at this ⊢
      linarith
    have hshi : sin φ ≤ (0.724612539412 : ℝ) := by
      have := sin_le_nine hφ0
      rw [hφdef] at this ⊢
      norm_num at this ⊢
      linarith
    have hchi : cos φ ≤ (0.689156526146 : ℝ) := by
      have := cos_le_eight hφ0
      rw [hφdef] at this ⊢
      norm_num at this ⊢
      linarith
    have htan := neg_cos_le_tangent (by norm_num [hφdef]) hφpi (le_of_lt hgt) hθ
    -- the constant term of the tangent line is negative
    have hprod : (3.14159265358979 - 101309 / 125000) * 0.724612123616 ≤ (π - φ) * sin φ := by
      apply mul_le_mul _ hslo (by norm_num) (by linarith)
      linarith
    have hconst : 1 + cos φ - (π - φ) * sin φ ≤ 0 := by
      norm_num at hprod
      linarith
    have h1 : 1 - cos θ ≤ θ * sin φ := by nlinarith
    -- `0.878565 · sin φ · π ≤ 2`
    have hsπ : (0.878565 : ℝ) * sin φ * π ≤ 2 := by
      have : sin φ * π ≤ 0.724612539412 * 3.14159265358980 := by
        apply mul_le_mul hshi (by linarith) (by linarith) (by norm_num)
      nlinarith
    rw [le_div_iff₀ hpi]
    have hθnn : 0 ≤ θ := hθ0
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 0.878565 * π / 2)]

/-! ### The constant -/

/-- **The Goemans–Williamson constant.** `α = inf_{0 < θ ≤ π} (2 / π) · θ / (1 - cos θ)`,
written as an infimum over the interval `(0, π]` (Goemans and Williamson, *J. ACM* 42(6)
(1995), 1115–1145, §2, p. 1121, where it is written as a minimum). -/
noncomputable def gwConstant : ℝ :=
  ⨅ θ : Ioc (0 : ℝ) π, 2 / π * ((θ : ℝ) / (1 - cos θ))

theorem one_sub_cos_pos {θ : ℝ} (h0 : 0 < θ) (h : θ ≤ π) : 0 < 1 - cos θ := by
  have := cos_lt_cos_of_nonneg_of_le_pi le_rfl h h0
  rw [cos_zero] at this
  linarith

private theorem bddBelow_ratio :
    BddBelow (range fun θ : Ioc (0 : ℝ) π => 2 / π * ((θ : ℝ) / (1 - cos θ))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨⟨θ, h0, h1⟩, rfl⟩
  have := one_sub_cos_pos h0 h1
  have := pi_pos
  positivity

/-- **The Goemans–Williamson constant is a lower bound for the ratio.** For
`0 < θ ≤ π`, `α ≤ (2 / π) · θ / (1 - cos θ)`. -/
theorem gwConstant_le {θ : ℝ} (h0 : 0 < θ) (h : θ ≤ π) :
    gwConstant ≤ 2 / π * (θ / (1 - cos θ)) :=
  ciInf_le bddBelow_ratio (⟨θ, h0, h⟩ : Ioc (0 : ℝ) π)

/-- **Goemans–Williamson Lemma 3.4, angle form.** For `0 ≤ θ ≤ π`,
`α · (1 - cos θ) / 2 ≤ θ / π` (Goemans and Williamson, *J. ACM* 42(6) (1995), Lemma 3.4,
before the change of variables `y = cos θ`). -/
theorem gwConstant_mul_le {θ : ℝ} (h0 : 0 ≤ θ) (h : θ ≤ π) :
    gwConstant * ((1 - cos θ) / 2) ≤ θ / π := by
  rcases eq_or_lt_of_le h0 with rfl | hpos
  · simp
  · have hc := one_sub_cos_pos hpos h
    have hpi := pi_pos
    have hle := mul_le_mul_of_nonneg_right (gwConstant_le hpos h)
      (le_of_lt (half_pos hc))
    calc gwConstant * ((1 - cos θ) / 2) ≤ 2 / π * (θ / (1 - cos θ)) * ((1 - cos θ) / 2) := hle
      _ = θ / π := by field_simp

/-- **Goemans–Williamson Lemma 3.4.** For `-1 ≤ y ≤ 1`,
`arccos y / π ≥ α · (1 - y) / 2` (Goemans and Williamson, *J. ACM* 42(6) (1995),
Lemma 3.4). -/
theorem gwConstant_mul_le_arccos_div_pi {y : ℝ} (h1 : -1 ≤ y) (h2 : y ≤ 1) :
    gwConstant * ((1 - y) / 2) ≤ arccos y / π := by
  have := gwConstant_mul_le (arccos_nonneg y) (arccos_le_pi y)
  rwa [cos_arccos h1 h2] at this

/-- **Goemans–Williamson Lemma 3.5.** `α > 0.87856` (Goemans and Williamson, *J. ACM* 42(6)
(1995), Lemma 3.5). The proof shows `α ≥ 0.878565`. -/
theorem lt_gwConstant : (0.87856 : ℝ) < gwConstant := by
  have hge : (0.878565 : ℝ) ≤ gwConstant := by
    have : Nonempty (Ioc (0 : ℝ) π) := ⟨⟨π, pi_pos, le_rfl⟩⟩
    refine le_ciInf fun ⟨θ, h0, h⟩ => ?_
    have hc := one_sub_cos_pos h0 h
    have hpi := pi_pos
    have hb := certified_mul_one_sub_cos_le (le_of_lt h0) h
    change (0.878565 : ℝ) ≤ 2 / π * (θ / (1 - cos θ))
    rw [show 2 / π * (θ / (1 - cos θ)) = (θ / π) / ((1 - cos θ) / 2) by field_simp]
    rw [le_div_iff₀ (half_pos hc)]
    exact hb
  linarith

/-- **The Goemans–Williamson constant is at most one.** Taking `θ = π` gives `α ≤ 1`. -/
theorem gwConstant_le_one : gwConstant ≤ 1 := by
  have h := gwConstant_le pi_pos le_rfl
  rw [cos_pi] at h
  have hpi := pi_pos
  calc gwConstant ≤ 2 / π * (π / (1 - -1)) := h
    _ = 1 := by field_simp; norm_num

end MathlibExt.Combinatorics.Optimization.GoemansWilliamson
