/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.OnlineGradientDescent
public import MathlibExt.Analysis.InnerProductSpace.ConvexProjection

open MathlibExt.Analysis.InnerProductSpace.ConvexProjection

/-- The first iterate is the projected gradient step. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (g : ℕ → E → E) (η : ℝ) (x0 : E) :
    ogdIter proj g η x0 1 = proj (x0 - η • g 0 x0) := rfl

/-- Boundary check `T = 0`: empty regret is nonpositive. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {proj : E → E} {f : ℕ → E → ℝ} {g : ℕ → E → E} {η : ℝ} (hη : 0 < η)
    (hproj : LipschitzWith 1 proj)
    (xstar : E) (hprojstar : proj xstar = xstar)
    (hsub : ∀ (t : ℕ) (x : E), f t x + @inner ℝ E _ (g t x) (xstar - x) ≤ f t xstar)
    (x0 : E) :
    ∑ t ∈ Finset.range 0, (f t (ogdIter proj g η x0 t) - f t xstar) ≤
      ‖x0 - xstar‖ ^ 2 / (2 * η) +
        (η / 2) * ∑ t ∈ Finset.range 0, ‖g t (ogdIter proj g η x0 t)‖ ^ 2 :=
  ogd_regret hη hproj xstar hprojstar hsub x0 0

/-- `ogd_regret` applies directly to the convex projection onto `Set.Icc 0 1`,
with zero costs and gradients: the `LipschitzWith 1` hypothesis is exactly
`lipschitzWith_convexProjection`. -/
example (x0 : ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T,
        ((fun _ _ => (0 : ℝ)) t
          (ogdIter (convexProjection (Set.Icc (0 : ℝ) 1)) (fun _ _ => 0) 1 x0 t)
          - (fun _ _ => (0 : ℝ)) t 0) ≤
      ‖x0 - 0‖ ^ 2 / (2 * 1) +
        (1 / 2) * ∑ t ∈ Finset.range T,
          ‖(fun _ _ => (0 : ℝ)) t
            (ogdIter (convexProjection (Set.Icc (0 : ℝ) 1)) (fun _ _ => 0) 1 x0 t)‖ ^ 2 := by
  have hKne : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  have hKc : IsComplete (Set.Icc (0 : ℝ) 1) := isCompact_Icc.isComplete
  have hKv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hproj : LipschitzWith 1 (convexProjection (Set.Icc (0 : ℝ) 1)) :=
    lipschitzWith_convexProjection hKne hKc hKv
  have hstar : convexProjection (Set.Icc (0 : ℝ) 1) 0 = 0 :=
    convexProjection_eq_self_of_mem hKne hKc hKv (by norm_num)
  have hsub : ∀ (t : ℕ) (x : ℝ),
      (fun _ _ => (0 : ℝ)) t x +
        @inner ℝ ℝ _ ((fun _ _ => (0 : ℝ)) t x) (0 - x) ≤ (fun _ _ => (0 : ℝ)) t 0 := by
    intro t x
    simp
  exact ogd_regret (by norm_num) hproj 0 hstar hsub x0 T
