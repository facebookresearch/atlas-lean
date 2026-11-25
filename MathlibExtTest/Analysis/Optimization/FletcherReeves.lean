/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Optimization.FletcherReeves
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.MetricSpace.Bounded

open MathlibExt.Analysis.Optimization.LineSearch
open WantedExt.Analysis.Optimization.FletcherReevesWanted
open scoped RealInnerProductSpace

local notation "f₂" => (fun y : ℝ => y ^ 2 / 2)

private theorem gradient_half_sq (y : ℝ) : gradient f₂ y = y := by
  rw [gradient_eq_deriv']
  have h : HasDerivAt f₂ (2 * y ^ 1 * 1 / 2) y :=
    ((hasDerivAt_id y).pow 2).div_const 2
  rw [h.deriv]
  ring

-- From `x 0 = 1`, this quadratic run halves each iterate. The curvature bound is attained
-- on every step, so the test uses the exact endpoint `σ = 1/2`.
example : ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, ‖gradient f₂ ((1 / 2 : ℝ) ^ k)‖ < ε := by
  let x (k : ℕ) := (1 / 2 : ℝ) ^ k
  let d (k : ℕ) := -(x k * (2 - x k))
  let α (k : ℕ) := 1 / (2 * (2 - x k))
  have hx0 : x 0 = 1 := pow_zero _
  have hxs (k : ℕ) : x (k + 1) = x k / 2 := by
    change (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k / 2
    rw [pow_succ, div_eq_mul_one_div ((1 / 2 : ℝ) ^ k)]
  have hxpos (k : ℕ) : 0 < x k := by dsimp [x]; positivity
  have hxle (k : ℕ) : x k ≤ 1 := by
    induction k with
    | zero => exact hx0.le
    | succ k ih => rw [hxs]; linarith
  have hden (k : ℕ) : 0 < 2 - x k := by linarith [hxle k]
  have hαd (k : ℕ) : α k * d k = -(x k / 2) := by
    dsimp only [α, d]
    field_simp [(hden k).ne']
  have hx (k : ℕ) : x (k + 1) = x k + α k • d k := by
    rw [hxs, smul_eq_mul, hαd]
    ring
  have hinner (a b : ℝ) : ⟪a, b⟫ = a * b := by
    simp [RCLike.inner_apply, mul_comm]
  refine fletcherReeves_liminf_norm_gradient (f := f₂) (δ := 1 / 4) (σ := 1 / 2) (L := 1)
    (x := x) (d := d) (α := α) (U := Set.univ) (by norm_num) (by norm_num) le_rfl
    (hlevel := ?_) (hlower := ?_) (hU := isOpen_univ) (hlevelU := Set.subset_univ _)
    (hdiff := ?_) (hlip := ?_) hx (fun k => div_pos zero_lt_one (mul_pos (by norm_num) (hden k)))
    ?_ ?_ ?_ (fun k => by rw [gradient_half_sq]; exact (hxpos k).ne')
  · refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := 1)).subset ?_
    intro y hy
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
    rw [sq_abs]
    change y ^ 2 / 2 ≤ x 0 ^ 2 / 2 at hy
    rw [hx0] at hy
    linarith
  · exact ⟨0, by rintro _ ⟨y, _, rfl⟩; positivity⟩
  · have h : Differentiable ℝ f₂ := (differentiable_id.pow 2).div_const 2
    exact h.differentiableOn
  · intro y _ z _
    rw [gradient_half_sq, gradient_half_sq, one_mul]
  · norm_num [d, hx0, gradient_half_sq]
  · intro k
    simp only [gradient_half_sq, Real.norm_eq_abs, sq_abs, smul_eq_mul, d, hxs]
    field_simp [(hxpos k).ne']
    ring
  · intro k
    constructor
    · unfold ArmijoCondition
      rw [← hx k, gradient_half_sq, hinner, hxs]
      calc
        _ ≤ f₂ (x k) + (1 / 4) * x k * (α k * d k) := by
          rw [hαd]
          dsimp only
          nlinarith [sq_nonneg (x k)]
        _ = _ := by ring
    · change |⟪gradient f₂ (x k + α k • d k), d k⟫| ≤ -(1 / 2) * ⟪gradient f₂ (x k), d k⟫
      rw [← hx k, gradient_half_sq, gradient_half_sq, hinner, hinner, hxs]
      have hdnonpos : d k ≤ 0 := neg_nonpos.mpr (mul_nonneg (hxpos k).le (hden k).le)
      rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hdnonpos)]
      exact le_of_eq (by ring)

/--
info: 'WantedExt.Analysis.Optimization.FletcherReevesWanted.fletcherReeves_liminf_norm_gradient'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fletcherReeves_liminf_norm_gradient
