/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.OnlineGradientDescent

/-- The first iterate is the projected gradient step. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (g : ℕ → E → E) (η : ℝ) (x0 : E) :
    ogdIter proj g η x0 1 = proj (x0 - η • g 0 x0) := rfl

/-- Boundary check `T = 0`: empty regret is nonpositive. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {proj : E → E} {f : ℕ → E → ℝ} {g : ℕ → E → E} {η : ℝ} (hη : 0 < η)
    (hproj : ∀ u v, ‖proj u - proj v‖ ≤ ‖u - v‖)
    (xstar : E) (hprojstar : proj xstar = xstar)
    (hsub : ∀ (t : ℕ) (x : E), f t x + @inner ℝ E _ (g t x) (xstar - x) ≤ f t xstar)
    (x0 : E) :
    ∑ t ∈ Finset.range 0, (f t (ogdIter proj g η x0 t) - f t xstar) ≤
      ‖x0 - xstar‖ ^ 2 / (2 * η) +
        (η / 2) * ∑ t ∈ Finset.range 0, ‖g t (ogdIter proj g η x0 t)‖ ^ 2 :=
  ogd_regret hη hproj xstar hprojstar hsub x0 0
