/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.ProjectedSubgradient

/-- The first iterate is the projected subgradient step (via `ogdIter`). -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (g : ℕ → E → E) (η : ℝ) (x0 : E) :
    ogdIter proj g η x0 1 = proj (x0 - η • g 0 x0) := rfl

/-- Boundary check `T = 1`: the average reduces to the initial point `x0`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {proj : E → E} {f : E → ℝ} {g : ℕ → E → E} {D G : ℝ}
    (hD : 0 < D) (hG : 0 < G)
    (hproj : ∀ u v, ‖proj u - proj v‖ ≤ ‖u - v‖)
    (xstar : E) (hprojstar : proj xstar = xstar)
    (hsub : ∀ (t : ℕ) (x y : E), f x + @inner ℝ E _ (g t x) (y - x) ≤ f y)
    (hg : ∀ (t : ℕ) (x : E), ‖g t x‖ ≤ G)
    (x0 : E) (hdist : ‖x0 - xstar‖ ≤ D) :
    f x0 - f xstar ≤ D * G := by
  simpa [ogdIter] using
    sgd_rate hD hG hproj xstar hprojstar hsub hg x0 hdist (T := 1) (by norm_num)
