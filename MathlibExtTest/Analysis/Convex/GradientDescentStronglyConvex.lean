/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.GradientDescentStronglyConvex
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace MathlibExt.Analysis.Convex.GradientDescentStronglyConvex

private noncomputable def q : ℝ → ℝ := fun x => (2 : ℝ)⁻¹ * x ^ 2

private theorem q_strong : StrongConvexOn Set.univ 1 q := by
  rw [strongConvexOn_iff_convex]
  refine (convexOn_const (0 : ℝ) convex_univ).congr fun x _ => ?_
  simp only [q, Real.norm_eq_abs, sq_abs]
  ring

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

-- The suboptimality bound `q x - q y ≤ ‖∇q(x)‖² / 2` for the `1`-strongly convex
-- `q x = x² / 2`.
example (x y : ℝ) : q x - q y ≤ x ^ 2 / 2 := by
  have h := sub_le_norm_sq_div_of_strongConvexOn one_pos q_strong
    (q_diff x).hasGradientAt y
  simpa [q_gradient, Real.norm_eq_abs, sq_abs] using h

-- Gradient descent on `x²/2` with step `1/2` halves the iterate, and the objective gap
-- contracts at least by the factor `1 - η m = 1/2` per step.
example (x₀ : ℝ) (k : ℕ) : q ((1 / 2 : ℝ) ^ k * x₀) ≤ (1 / 2 : ℝ) ^ k * q x₀ := by
  let X : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * x₀
  have hX : ∀ k, X (k + 1) = X k - (1 / 2 : ℝ) • gradient q (X k) := by
    intro k
    rw [q_gradient]
    simp only [X, pow_succ, smul_eq_mul]
    ring
  have hrate := gradient_descent_strongly_convex_linear_rate (L := 1) (m := 1) one_pos one_pos
    q_strong q_diff q_lip (η := 1 / 2) (by norm_num) hX 0 k
  have hq0 : q 0 = 0 := by simp [q]
  simp only [X, pow_zero, one_mul, hq0, sub_zero] at hrate
  norm_num at hrate ⊢
  exact hrate

end MathlibExt.Analysis.Convex.GradientDescentStronglyConvex
