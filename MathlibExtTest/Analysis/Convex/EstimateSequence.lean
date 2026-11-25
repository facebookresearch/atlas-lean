/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.EstimateSequence
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Mul

namespace MathlibExt.Analysis.Convex.EstimateSequence

/-! Non-vacuity tests on `q x = x² / 2` over `ℝ`, which is `1`-smooth and `1`-strongly convex. -/

private noncomputable def q : ℝ → ℝ := fun x => (2 : ℝ)⁻¹ * x ^ 2

private theorem q_strong : StrongConvexOn Set.univ 1 q := by
  rw [strongConvexOn_iff_convex]
  refine (convexOn_const (0 : ℝ) convex_univ).congr fun x _ => ?_
  simp only [q, Real.norm_eq_abs, sq_abs]
  ring

private theorem q_convex : StrongConvexOn Set.univ 0 q := by
  rw [strongConvexOn_iff_convex]
  have h : ConvexOn ℝ Set.univ (fun x : ℝ => (2 : ℝ)⁻¹ * x ^ 2) := by
    simpa [smul_eq_mul] using
      ((Even.convexOn_pow (𝕜 := ℝ) even_two)).smul (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  refine h.congr fun x _ => ?_
  simp [q]

private theorem q_diff : Differentiable ℝ q := by
  unfold q; fun_prop

private theorem q_gradient (x : ℝ) : gradient q x = x := by
  have h : HasDerivAt q x x := by
    have := (hasDerivAt_pow 2 x).const_mul (2⁻¹ : ℝ)
    unfold q
    convert this using 1
    norm_num; ring
  rw [gradient_eq_deriv', h.deriv]

private theorem q_lip : LipschitzWith (1 : NNReal) (gradient q) := by
  rw [show gradient q = id by ext x; exact q_gradient x]
  exact LipschitzWith.id

/-! ### The general scheme with `μ = 0`, `L = 1`, `γ 0 = L = 1`: the `α k` vary with `k`. -/

/-- The root `α ∈ (0, 1)` of `α ^ 2 = (1 - α) γ` (the equation of step 1a with `L = 1`, `μ = 0`). -/
private noncomputable def alphaOf (γ : ℝ) : ℝ := (√(γ ^ 2 + 4 * γ) - γ) / 2

private theorem alphaOf_spec {γ : ℝ} (hγ : 0 < γ) :
    0 < alphaOf γ ∧ alphaOf γ < 1 ∧ 1 * alphaOf γ ^ 2 = (1 - alphaOf γ) * γ + alphaOf γ * 0 := by
  have hs : √(γ ^ 2 + 4 * γ) ^ 2 = γ ^ 2 + 4 * γ := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ √(γ ^ 2 + 4 * γ) := Real.sqrt_nonneg _
  have hgt : γ < √(γ ^ 2 + 4 * γ) := by nlinarith
  have hlt : √(γ ^ 2 + 4 * γ) < γ + 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · unfold alphaOf; linarith
  · unfold alphaOf; linarith
  · unfold alphaOf; nlinarith

private noncomputable def gam : ℕ → ℝ
  | 0 => 1
  | k + 1 => (1 - alphaOf (gam k)) * gam k

private theorem gam_pos : ∀ k, 0 < gam k
  | 0 => by simp [gam]
  | k + 1 => by
    have h := alphaOf_spec (gam_pos k)
    simp only [gam]
    have : 0 < 1 - alphaOf (gam k) := by linarith [h.2.1]
    exact mul_pos this (gam_pos k)

/-- The pair `(x k, v k)`; `y k = α k v k + (1 - α k) x k` and `x (k + 1) = y k - ∇q (y k)`. -/
private noncomputable def st : ℕ → ℝ × ℝ
  | 0 => (1, 1)
  | k + 1 =>
    let a := alphaOf (gam k)
    let y := a * (st k).2 + (1 - a) * (st k).1
    (y - y, ((1 - a) * gam k * (st k).2 - a * y) / ((1 - a) * gam k))

private noncomputable def ys (k : ℕ) : ℝ :=
  alphaOf (gam k) * (st k).2 + (1 - alphaOf (gam k)) * (st k).1

private theorem scheme :
    IsNesterovScheme q 1 0 (fun k => alphaOf (gam k)) gam (fun k => (st k).1) ys
      (fun k => (st k).2) where
  alpha_pos k := (alphaOf_spec (gam_pos k)).1
  alpha_le_one k := (alphaOf_spec (gam_pos k)).2.1.le
  gamma_zero_pos := by simp [gam]
  gamma_succ k := by simp [gam]
  alpha_sq k := by
    have h := (alphaOf_spec (gam_pos k)).2.2
    simp only [gam]; linarith
  v_zero := by simp [st]
  y_eq k := by
    simp only [ys, gam, smul_eq_mul]; ring
  descent k := by
    simp only [st, q_gradient, q, Real.norm_eq_abs, sq_abs, ys]
    ring_nf; rfl
  v_succ k := by
    have h := alphaOf_spec (gam_pos k)
    have hne : (1 - alphaOf (gam k)) * gam k ≠ 0 :=
      (mul_pos (by linarith [h.2.1]) (gam_pos k)).ne'
    change gam (k + 1) * (st (k + 1)).2 = ((1 - alphaOf (gam k)) * gam k) * (st k).2 +
      (alphaOf (gam k) * 0) * ys k - alphaOf (gam k) * gradient q (ys k)
    rw [show gam (k + 1) = (1 - alphaOf (gam k)) * gam k from rfl,
      show (st (k + 1)).2 = ((1 - alphaOf (gam k)) * gam k * (st k).2 - alphaOf (gam k) * ys k) /
        ((1 - alphaOf (gam k)) * gam k) from rfl, mul_div_cancel₀ _ hne, q_gradient]
    ring

-- Theorem 2.2.2 instantiated on this run: the gap at `x k` is at most `4 / (k + 2) ^ 2`.
example (k : ℕ) : q (st k).1 ≤ 1 * min ((1 - √(0 / 1)) ^ k) (4 / ((k : ℝ) + 2) ^ 2) * 1 := by
  have h := estimateSequence_optimal_rate scheme one_pos le_rfl zero_le_one q_convex q_diff
    (by exact q_lip) (by simp [gam]) (xstar := 0)
    (fun z => by simp only [q]; nlinarith [sq_nonneg z]) k
  have hq0 : q 0 = 0 := by simp [q]
  simpa [hq0, st] using h

-- The `α k` are not constant: `α 0 = (√5 - 1) / 2` and `γ 1 = α 0 ^ 2 ≠ 1`.
example : gam 1 ≠ gam 0 := by
  have h := alphaOf_spec (gam_pos 0)
  simp only [gam] at h ⊢
  intro heq
  have : alphaOf 1 = 0 := by nlinarith
  linarith [h.1]

/-! ### The strongly convex constant-step method with `μ = 1`, `L = 4`, `q = √(1 / 4) = 1 / 2`. -/

private noncomputable def sc : ℕ → ℝ × ℝ
  | 0 => (3, 3)
  | k + 1 =>
    let y := (1 + √(1 / 4 : ℝ))⁻¹ * ((sc k).1 + √(1 / 4 : ℝ) * (sc k).2)
    (y - (1 / 4) * y, (1 - √(1 / 4 : ℝ)) * (sc k).2 + √(1 / 4 : ℝ) * y - (√(1 / 4 : ℝ) / 1) * y)

example (u : ℝ) (k : ℕ) :
    q (sc k).1 - q u ≤
      (1 - √(1 / 4 : ℝ)) ^ k * (q (sc 0).1 - q u + 1 / 2 * ‖(sc 0).1 - u‖ ^ 2) := by
  have hlip : LipschitzWith ⟨4, by norm_num⟩ (gradient q) :=
    q_lip.weaken (NNReal.coe_le_coe.mp (by change (1 : ℝ) ≤ 4; norm_num))
  exact accelerated_strongly_convex_rate (L := 4) (μ := 1) (by norm_num) one_pos (by norm_num)
    q_strong q_diff hlip (y := fun k => (1 + √(1 / 4 : ℝ))⁻¹ • ((sc k).1 + √(1 / 4 : ℝ) • (sc k).2))
    (by simp [sc]) (fun k => rfl)
    (fun k => by simp only [sc, q_gradient, smul_eq_mul])
    (fun k => by simp only [sc, q_gradient, smul_eq_mul]) u k

end MathlibExt.Analysis.Convex.EstimateSequence
