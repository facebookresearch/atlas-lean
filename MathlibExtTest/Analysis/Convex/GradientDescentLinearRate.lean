/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.GradientDescentLinearRate

/-- The first iterate is exactly one gradient step. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → E) (L : ℝ) (x0 : E) :
    gdIter g L x0 1 = x0 - (L⁻¹ : ℝ) • g x0 := rfl

/-- Boundary check `k = 0`: the rate bound is the initial gap. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {g : E → E} {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hsmooth : ∀ x y, f y ≤ f x + @inner ℝ E _ (g x) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
    (hstrong : ∀ x y, f x + @inner ℝ E _ (g x) (y - x) + (μ / 2) * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x0 : E) :
    f (gdIter g L x0 0) - f xstar ≤ (1 - μ / L) ^ 0 * (f x0 - f xstar) :=
  gd_linear_rate hμ hμL hsmooth hstrong xstar hmin x0 0

/-- The quadratic `x²`, with gradient `2x`, has a nonzero contraction factor
when `μ = 2` and `L = 4`. The rate theorem bounds its second iterate. -/
example : (gdIter (fun x : ℝ => 2 * x) 4 2 2) ^ 2 ≤ 1 := by
  have hsmooth : ∀ x y : ℝ,
      y ^ 2 ≤ x ^ 2 + inner ℝ (2 * x) (y - x) + (4 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
    intro x y
    simp only [Real.inner_apply, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (y - x)]
  have hstrong : ∀ x y : ℝ,
      x ^ 2 + inner ℝ (2 * x) (y - x) + (2 / 2 : ℝ) * ‖y - x‖ ^ 2 ≤ y ^ 2 := by
    intro x y
    simp only [Real.inner_apply, Real.norm_eq_abs, sq_abs]
    nlinarith
  have hmin : ∀ y : ℝ, (0 : ℝ) ^ 2 ≤ y ^ 2 := by
    intro y
    simpa using sq_nonneg y
  convert gd_linear_rate (f := fun x : ℝ => x ^ 2)
    (g := fun x : ℝ => 2 * x) (L := 4) (μ := 2) (by norm_num) (by norm_num)
    hsmooth hstrong 0 hmin 2 2 using 1 <;> norm_num
