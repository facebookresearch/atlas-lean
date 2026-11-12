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
