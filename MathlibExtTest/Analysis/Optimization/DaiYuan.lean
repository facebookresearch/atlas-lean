/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Optimization.DaiYuan
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

open MathlibExt.Analysis.Optimization.DaiYuan MathlibExt.Analysis.Optimization.LineSearch

-- With `g = 2`, `g' = 1` and `d = -1` in `ℝ`: `β = 1 / ((-1) (1 - 2)) = 1`.
example : daiYuanBeta (2 : ℝ) 1 (-1) = 1 := by
  norm_num [daiYuanBeta]

-- The identity `⟪g', d'⟫ = β ⟪g, d⟫` on these values: both sides equal `-2`.
example : inner ℝ (1 : ℝ) (-1 + daiYuanBeta (2 : ℝ) 1 (-1) • (-1 : ℝ)) =
    daiYuanBeta (2 : ℝ) 1 (-1) * inner ℝ (2 : ℝ) (-1) :=
  inner_daiYuan_direction (by norm_num)

-- The curvature condition with `σ = 1/2` holds (`⟪g', d⟫ = -1 ≥ -1 = σ ⟪g, d⟫`), so the next
-- Dai–Yuan direction is again a descent direction.
example : inner ℝ (1 : ℝ) (-1 + daiYuanBeta (2 : ℝ) 1 (-1) • (-1 : ℝ)) < 0 :=
  (inner_daiYuan_direction_neg (σ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).2

private theorem gradient_half_sq (y : ℝ) : gradient (fun x : ℝ => x ^ 2 / 2) y = y := by
  rw [gradient_eq_deriv']
  have : HasDerivAt (fun x : ℝ => x ^ 2 / 2) (2 * y ^ 1 * 1 / 2) y :=
    ((hasDerivAt_id y).pow 2).div_const 2
  rw [this.deriv]; ring

-- Non-vacuity of the main theorem: the Dai–Yuan method on `f x = x² / 2` from `x 0 = 1`, with
-- `α 0 = 1/2` and `α k = 1/4` afterwards, gives `x k = 2⁻ᵏ`, `d 0 = -1` and `d k = -2 x k`; every
-- step satisfies the standard Wolfe conditions with `δ = 1/4` and `σ = 1/2`, and `L = 1`.
example : ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N,
    ‖gradient (fun x : ℝ => x ^ 2 / 2) ((1 / 2 : ℝ) ^ k)‖ < ε := by
  set x : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k with hxdef
  set d : ℕ → ℝ := fun k => if k = 0 then -1 else -2 * (1 / 2 : ℝ) ^ k with hddef
  set α : ℕ → ℝ := fun k => if k = 0 then 1 / 2 else 1 / 4 with hαdef
  have hxpos : ∀ k, 0 < x k := fun k => by simp only [hxdef]; positivity
  have hxs : ∀ k, x (k + 1) = x k / 2 := fun k => by simp only [hxdef, pow_succ]; ring
  have hd0 : d 0 = -x 0 := by simp [hddef, hxdef]
  have hds : ∀ k, d (k + 1) = -2 * x (k + 1) := fun k => by simp [hddef, hxdef]
  have hα0 : α 0 = 1 / 2 := by simp [hαdef]
  have hαs : ∀ k, α (k + 1) = 1 / 4 := fun k => by simp [hαdef]
  have hx0 : x 0 = 1 := by simp [hxdef]
  have hx : ∀ k, x (k + 1) = x k + α k • d k := by
    intro k
    rcases k with _ | k
    · rw [hxs, hα0, hd0, hx0, smul_eq_mul]; norm_num
    · rw [hxs, hαs, hds, hxs, smul_eq_mul]; ring
  have hinner : ∀ a b : ℝ, inner ℝ a b = a * b := fun a b => by
    simp only [RCLike.inner_apply, conj_trivial]; ring
  refine daiYuan_liminf_norm_gradient
    (f := fun x : ℝ => x ^ 2 / 2) (δ := 1 / 4) (σ := 1 / 2) (L := 1) (x := x) (d := d) (α := α)
    (by norm_num) (by norm_num) (by norm_num) hx
    (fun k => by rcases k with _ | k <;> simp [hα0, hαs]) (by rw [hd0, gradient_half_sq]) ?_ ?_ ?_
    ?_ ?_
  · intro k
    have := hxpos k
    rw [gradient_half_sq, gradient_half_sq, daiYuanBeta, hinner, Real.norm_eq_abs, sq_abs, hds]
    rcases k with _ | k
    · simp only [hd0, hxs, hx0]; norm_num
    · have := (hxpos k).ne'
      simp only [hds, hxs]
      field_simp
      ring
  · intro k
    have := hxpos k
    refine ⟨?_, ?_⟩
    · unfold ArmijoCondition
      rw [← hx k, gradient_half_sq, hinner, hxs]
      rcases k with _ | k
      · rw [hα0, hd0]; nlinarith
      · rw [hαs, hds, hxs]; nlinarith
    · unfold CurvatureCondition
      rw [← hx k, gradient_half_sq, gradient_half_sq, hinner, hinner, hxs]
      rcases k with _ | k
      · rw [hd0]; nlinarith
      · rw [hds, hxs]; nlinarith
  · intro k
    rw [gradient_half_sq, gradient_half_sq, one_mul]
  · exact ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩
  · intro k
    rw [gradient_half_sq]
    exact (hxpos k).ne'
